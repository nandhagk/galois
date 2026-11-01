# Galois.Domains

## Selectable known-bit multiplication (DOM-8)

`DomainsKnownBitsFast.v` adds a selectable `word_domain tnum` using the existing lattice,
concretisation and all existing transfers except multiplication. This is a precision choice:
it has the same soundness interface, but need not return the same abstract fact as DOM-2.
No existing public definition or theorem changes. The multiplication is a width-bounded
shift-and-add algorithm over tnums, processing multiplier bits from least to most significant.
Start at the constant zero tnum. For each bit, leave the accumulator unchanged when the bit is
known zero; add the shifted multiplicand with the DOM-2 tnum addition when it is known one;
and join the unchanged accumulator with that sum when the bit is unknown. Truncate each shift
and addition to the result width. A contradictory input mask returns the tnum bottom. Constants
therefore yield the exact concrete product. Iteration uses binary fuel or a structurally bounded
bit traversal and does not enumerate concrete operands.

```coq
Definition tnum_mul_precise (w : width) (a b : tnum) : tnum.
Definition known_bits_precise_domain : word_domain tnum.
(* Same fields as known_bits_domain except pforward bvmul on two operands of width rw uses
   tnum_mul_precise; all other inputs use pforward known_bits_domain unchanged. *)
Theorem tnum_mul_precise_sound (w : width) (a b : tnum) (x y : Z) :
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_mul_precise w a b) (wmul w x y).
Theorem known_bits_precise_word_laws : word_laws known_bits_precise_domain tnum_gamma.
Theorem tnum_mul_precise_constants (w : width) (x y : Z) :
  tnum_mul_precise w (pconst known_bits_domain w x) (pconst known_bits_domain w y) =
  pconst known_bits_domain w (wmul w x y).
```

The implementation proves the claims directly for all widths and the repository's total word
semantics. It does not claim an optimal abstract multiplication or equal results to DOM-2.
Card: DOM-8.

Domains provides abstract values for machine words and for memory, all proved sound once. A
`numeric_domain` is a record of a lattice, an abstraction of constants, a forward transfer for
every `Bits` operator and a backward `assume` that refines operands from a known result; one
generic theorem lifts a domain's operator soundness to whole `Bits.expr` evaluation. Instances are
constants, intervals, signs, known bits, wrapping intervals and congruences, reduced products of
them, demanded bits (a backward agreement domain), and the memory domains for addresses,
points-to sets and byte ranges, plus equality partitions and symbolic keys. For example, with known
bits, after `x := y & 0xF0` on 8-bit words the low nibble of `x` is known to be zero:

```coq
(* forward D bvand [top_at D 8; of_const D 8 240]  describes words with bits 0..3 known 0 *)
(* assume D bvult (of_const D 1 1) [x; of_const D 8 10]  refines x to [0, 9] in an interval domain *)
```

Conventions of this document. Statements sit in `Section`s whose `Context` and `Variables` lines
declare what they mention, and a `(* Proof idea ... Card ... *)` line follows each group of
theorems. Order and Bits names are used as in their documents: `lattice`, `leb`, `concretisation`,
`gamma`, `bottom_empty`, `top_full`, `agreement`, `word` (`width * Z`), `eval_op`, `eval`, `wrap`,
`is_word`. The expression names `expr` and `eval` are imported from `Bits`. The `numeric_domain`
field for the full set of one width is `top_at`, because `top` is the
Order record. Stdlib imports (`ZArith`, `List`, `Bool`, `Sorting.Sorted`) are implicit.

## Files

| File | Contents | Card |
|---|---|---|
| `DomainsNumeric.v` | `numeric_domain`, `numeric_laws`, `word_domain`, `word_laws`, `tagged`, `capped`, `capped_domain`, `abs_eval`, `abs_assume`, the generic soundness theorems | DOM-1a |
| `DomainsConst.v` | constants (flat) | DOM-1a |
| `DomainsInterval.v` | intervals over `Z` with infinite bounds, threshold widening, narrowing | DOM-1b |
| `DomainsSign.v` | signs | DOM-1a |
| `DomainsKnownBits.v` | known bits (tnum) | DOM-2 |
| `DomainsKnownBitsFast.v` | selectable tnum multiplication | DOM-8 |
| `DomainsSignedBounds.v` | sign-separated bit and interval reduction | DOM-9 |
| `DomainsSignedBoundsDomain.v` | selectable signed bit-and-bounds domain and queries | DOM-9 |
| `DomainsWrapped.v` | wrapping intervals with a widening rank | DOM-3 |
| `DomainsCongruence.v` | congruences | DOM-4 |
| `DomainsProduct.v` | the reduced-product functor and its three reductions | DOM-4 |
| `DomainsDemanded.v` | masks, `mask_agreement`, `demand` | DOM-5 |
| `DomainsAddress.v` | addresses, `covers`, `disjoint`, `may_overlap` | DOM-6 |
| `DomainsPointsTo.v` | points-to sets | DOM-6 |
| `DomainsByteRange.v` | byte-range sets | DOM-6 |
| `DomainsFootprint.v` | `footprint`, `covered`, `footprint_encoding`, canonical footprint lists, `range_must` and its lattice | DOM-6 |
| `DomainsEquality.v` | equality partitions over `UnionFind` | DOM-7 |
| `DomainsSymbolic.v` | symbolic hash-consed keys over `Table` | DOM-7 |

Prerequisites. DOM-1a needs ORD-1 and BIT-1; DOM-1b needs DOM-1a; DOM-2 and DOM-3 need DOM-1a and
BIT-2; the landed DOM-3 also reuses DOM-1b interval definitions and soundness lemmas. DOM-4 needs
DOM-2, DOM-3 and DOM-1b (`interval_cong_domain`); DOM-5 needs ORD-1 and BIT-2;
DOM-6
needs ORD-2 and DOM-1b (an address holds an `interval`); DOM-7 needs ORD-1, COL-2 and BIT-1.

## Definitions

### The numeric-domain interface (`DomainsNumeric.v`)

An element of `A` describes a set of words (pairs `(w, z)` of a width and a value). `forward` and
`assume` may return anything when `eval_op` would return `None`: there is no concrete result to
approximate. `assume` always returns one entry per input operand, even when evaluation would return
`None`. `meet` is an addition to the brief's field list: guards need it to refine a variable that is
read directly.

```coq
Record numeric_domain (A : Type) : Type := NumericDomain {
  lat : lattice A;
  top_at : width -> A;                       (* every word of that width *)
  of_const : width -> Z -> A;
  forward : op -> list A -> A;
  assume : op -> A -> list A -> list A;      (* assume o r xs: refine xs given that the result is in r *)
  meet : A -> A -> A
}.
Record numeric_laws {A} (D : numeric_domain A) (G : concretisation A word) : Prop := {
  lat_laws : lattice_laws (lat D);
  gamma_laws : concretisation_laws (lat D) G;
  bot_empty : bottom_empty (lat D) G;
  top_at_sound : forall w z, is_word w z -> gamma G (top_at D w) (w, z);
  of_const_sound : forall w z, gamma G (of_const D w z) (w, wrap w z);
  forward_sound : forall o xs ys r, Forall2 (gamma G) xs ys -> eval_op o ys = Some r ->
    gamma G (forward D o xs) r;
  assume_sound : forall o a xs ys r, Forall2 (gamma G) xs ys -> eval_op o ys = Some r ->
    gamma G a r -> Forall2 (gamma G) (assume D o a xs) ys;
  assume_length : forall o a xs, List.length (assume D o a xs) = List.length xs;
  assume_refines : forall o a xs,
    Forall2 (fun x' x => leb (lat D) x' x = true) (assume D o a xs) xs;
  meet_sound : forall a b c, gamma G a c -> gamma G b c -> gamma G (meet D a b) c;
  meet_lower_left : forall a b, leb (lat D) (meet D a b) a = true
}.
(* There is no right lower bound: a meet may over-approximate the intersection by its first argument
   (wrapped intervals), so it is below the first argument only. *)
```

Evaluation over expressions. `abs_eval` and `abs_assume` are structurally recursive with an inner
`fix` over the argument list (a `List.map` of the recursive call is rejected by the guard checker).

```coq
Fixpoint abs_eval {A} (D : numeric_domain A) (env : nat -> A) (e : expr) : A.
(* Var i -> env i; Const w z -> of_const D w z; App o args -> forward D o (the abs_eval of each arg) *)
Fixpoint abs_assume {A} (D : numeric_domain A) (env : nat -> A) (e : expr) (a : A) : nat -> A.
(* the environment refined by the fact that e's value is in a.
   Var i -> env with i set to meet D (env i) a; Const -> env;
   App o args -> let xs' := assume D o a (the abs_eval of each arg) in the arguments are refined
   one after another, each by its entry of xs', each seeing the environment refined so far *)
Definition env_ok (cenv : nat -> word) : Prop := forall i, is_word (fst (cenv i)) (snd (cenv i)).
Definition env_sound {A} (G : concretisation A word) (aenv : nat -> A) (cenv : nat -> word) : Prop :=
  forall i, gamma G (aenv i) (cenv i).
```

### Payload domains and width tags (`DomainsNumeric.v`)

Most instances describe a set of values without saying their width, and need the width to compute
(wrap-around, sign). A `word_domain` supplies width-indexed operations over a payload `P`; the
builder `tagged_domain` adds the width plumbing once and yields a `numeric_domain`.

```coq
Record word_domain (P : Type) : Type := WordDomain {
  plat : width -> lattice P;
  ptop : width -> P;
  pconst : width -> Z -> P;
  pforward : op -> list (width * P) -> width -> P;          (* operands with widths, result width *)
  passume : op -> list (width * P) -> width -> P -> list P;  (* ..., result width, result fact *)
  pmeet : width -> P -> P -> P
}.
Definition payload_sound {P} (G : width -> P -> Z -> Prop) (wp : width * P) (y : word) : Prop :=
  fst wp = fst y /\ is_word (fst y) (snd y) /\ G (fst wp) (snd wp) (snd y).
Record word_laws {P} (D : word_domain P) (G : width -> P -> Z -> Prop) : Prop := {
  plat_laws : forall w, lattice_laws (plat D w);
  pgamma_monotone : forall w a b z, leb (plat D w) a b = true -> G w a z -> G w b z;
  pgamma_bot_empty : forall w z, ~ G w (bot (plat D w)) z;
  ptop_sound : forall w z, is_word w z -> G w (ptop D w) z;
  pconst_sound : forall w z, G w (pconst D w z) (wrap w z);
  pforward_sound : forall o wps ys rw z, Forall2 (payload_sound G) wps ys ->
    eval_op o ys = Some (rw, z) -> G rw (pforward D o wps rw) z;
  passume_sound : forall o wps ys rw z q, Forall2 (payload_sound G) wps ys ->
    eval_op o ys = Some (rw, z) -> G rw q z ->
    Forall2 (fun p y => G (fst p) (snd p) (snd y)) (List.combine (List.map fst wps)
      (passume D o wps rw q)) ys;
  passume_refines : forall o wps rw q,
    Forall2 (fun wp p' => leb (plat D (fst wp)) p' (snd wp) = true) wps (passume D o wps rw q);
  pmeet_sound : forall w a b z, G w a z -> G w b z -> G w (pmeet D w a b) z;
  pmeet_lower_left : forall w a b, leb (plat D w) (pmeet D w a b) a = true
}.

Inductive tagged (P : Type) : Type :=
  | TBot
  | TVal (w : width) (p : P)
  | TAny.
Definition tagged_lattice {P} (plat : width -> lattice P) : lattice (tagged P).
(* TBot <= everything; everything <= TAny; TVal w a <= TVal w' b iff w = w' and leb (plat w) a b;
   nothing else. In particular no TVal is <= TBot and TAny <= TVal _ _ is false: an "a <= bot"
   disjunct, in either clause, would break transitivity through TBot (TVal 8 a <= TBot <= TVal 16 b).
   join and widen: TBot neutral, TAny absorbs, equal widths use the payload's join (widen),
   different widths give TAny. narrow (TVal w a) (TVal w b) uses the payload's narrow, else the
   first argument *)
Definition tagged_val {P} (D : word_domain P) (w : width) (p : P) : tagged P :=
  if leb (plat D w) p (bot (plat D w)) then TBot else TVal w p.         (* an empty payload is TBot *)
Definition tagged_domain {P} (D : word_domain P) : numeric_domain (tagged P).
(* top_at w = TVal w (ptop w); of_const w z = TVal w (pconst w z);
   forward o xs: an operand TBot, or TVal _ p with leb p bot -> TBot; all TVal wi pi and
     result_width o [wi] = Some rw -> tagged_val rw (pforward o [(wi, pi)] rw); all TVal with no
     result width -> TBot; otherwise (some TAny) TAny.
   assume o a xs: a is TBot, or TVal _ q with leb q bot -> every operand TBot; a = TVal rw q and
     every x = TVal wi pi with result_width o [wi] = Some rw -> each operand TVal wi pi becomes
     tagged_val wi (its entry of passume), so the result has the length of xs; a = TVal _ _, all
     operands TVal and no matching result width -> every operand TBot; otherwise xs unchanged.
   meet: TBot absorbs, TAny neutral, equal widths tagged_val w (pmeet w p q), different widths TBot.
   So forward, meet and assume return TBot whenever a payload is <= bot *)
Definition tagged_gamma {P} (G : width -> P -> Z -> Prop) : concretisation (tagged P) word.
(* TBot: nothing; TVal w p: (w', z) with w' = w, is_word w z and G w p z; TAny: every word *)
```

Termination needs a bound on ranks, which no single bound gives over all widths. `capped` restricts
the carrier to widths up to a cap, which is a program's real situation:

```coq
Definition width_ok {P} (maxw : width) (t : tagged P) : Prop :=
  match t with TVal w _ => (w <= maxw)%positive | _ => True end.
Definition capped {P} (maxw : width) : Type := { t : tagged P | width_ok maxw t }.
Definition capped_lattice {P} (maxw : width) (plat : width -> lattice P) : lattice (@capped P maxw).
Definition capped_height {P} (D : word_domain P) (maxw : width)
  (laws : forall w, lattice_laws (plat D w))
  (H : forall w, monotone_height (plat D w)) :
  monotone_height (capped_lattice maxw (plat D)).
Definition capped_wrank {P} (D : word_domain P) (maxw : width)
  (W : forall w, bounded_widening_rank (plat D w)) :
  bounded_widening_rank (capped_lattice maxw (plat D)).
(* with M the maximum, over the widths 1..maxw, of the payload bound (resp. wbound):
   capped_height: rank TBot = 0, TVal w p = 1 + the payload's rank, TAny = 2 + M; bound 2 + M;
   capped_wrank: wrank TAny = 0, TVal w p = 1 + the payload's wrank, TBot = 2 + M; wbound 2 + M *)

(* The domain over the capped carrier: the tagged domain with every result clamped. *)
Definition clamp {P} (maxw : width) (t : tagged P) : @capped P maxw.
(* t when width_ok maxw t; a TVal w _ with w > maxw becomes TAny *)
Definition capped_domain {P} (D : word_domain P) (maxw : width) : numeric_domain (@capped P maxw).
(* lat = capped_lattice maxw (plat D). top_at, of_const, forward and meet are those of
   tagged_domain D on the underlying values followed by clamp maxw, so in every operation a
   TVal w _ with w > maxw becomes TAny (top_at w for w > maxw is TAny; a bvzext or bvconcat that
   leaves the cap gives TAny). assume is that of tagged_domain D with each refined operand clamped:
   an operand within the cap refines within the cap, so the clamp changes nothing there *)
Definition capped_gamma {P} (G : width -> P -> Z -> Prop) (maxw : width) :
  concretisation (@capped P maxw) word.                 (* gamma t c = tagged_gamma G (proj1_sig t) c *)
```

### Constants, intervals, signs (DOM-1a: constants and signs; DOM-1b: intervals)

```coq
(* DomainsConst.v (DOM-1a): the payload is flat Z, the width lives in the tag *)
Definition const_domain : word_domain (flat Z).
(* plat _ = flat_lattice Z.eqb; ptop _ = FTop; pconst w z = FVal (wrap w z).
   pforward: all operands FVal -> FVal of the eval_op value (FBot if eval_op is None); some FBot
     -> FBot; otherwise FTop, except the annihilators: bvmul and bvand with a FVal 0 operand give
     FVal 0, bvor with an all-ones operand gives all ones, bvshl bvlshr bvashr bvurem with first
     operand FVal 0 give FVal 0.
   passume: bveq with result FVal 1 and bvne with result FVal 0 give each operand the other's
     constant when known; bvadd bvsub bvxor bvnot bvneg with the result and all but one operand known
     solve the remaining operand; every refinement uses pmeet with the old operand; otherwise
     unchanged.
   pmeet: FBot absorbs, FTop neutral, FVal a with FVal b is FVal a if a = b, else FBot *)
Definition const_gamma (w : width) (p : flat Z) (z : Z) : Prop :=
  match p with FBot => False | FVal c => z = c | FTop => True end.

(* DomainsInterval.v (DOM-1b): intervals of integers with infinite bounds *)
Inductive bound : Type :=
  | NegInf
  | Fin (z : Z)
  | PosInf.
Inductive interval : Type :=
  | IBot
  | Itv (lo hi : bound).
Definition interval_lattice (thresholds : list Z) : lattice interval.
(* bounds order NegInf < Fin z < PosInf. IBot <= everything; Itv l1 h1 <= Itv l2 h2 iff l2 <= l1
   and h1 <= h2. join: the hull. widen a b: IBot neutral; a bound that moved outward jumps to the
   nearest threshold beyond it, or to the infinity if there is none; a bound that did not move
   stays. narrow (Itv l1 h1) (Itv l2 h2): an infinite bound of the first is replaced by the
   second's, a finite one is kept; narrow IBot _ = IBot; narrow a IBot = a *)
Definition interval_gamma : concretisation interval Z.        (* IBot: nothing; Itv lo hi: lo <= z <= hi *)
Definition interval_wrank (thresholds : list Z) : bounded_widening_rank (interval_lattice thresholds).
(* lower: NegInf 0, Fin z 1 + #{t in thresholds | t < z}, PosInf 1 + length thresholds;
   upper: PosInf 0, Fin z 1 + #{t | z < t}, NegInf 1 + length thresholds;
   wrank (Itv l h) = lower l + upper h; wrank IBot = wbound = 2 * (length thresholds + 1) + 1 *)
Definition interval_pgamma (w : width) (i : interval) (z : Z) : Prop :=
  is_word w z /\ gamma interval_gamma i z.                  (* unsigned view of the word *)
Definition interval_domain (thresholds : list Z) : word_domain interval.
(* plat _ = interval_lattice thresholds; ptop w = Itv (Fin 0) (Fin (modulus w - 1));
   pconst w z = the point wrap w z; pmeet = intersection (IBot if empty). Rules below. *)

(* DomainsSign.v (DOM-1a) *)
Record sign : Type := Sign { neg : bool; zero : bool; pos : bool }.
Definition sign_lattice : lattice sign.      (* field-wise implication; bot all false; join = widen = field-wise orb *)
Definition sign_height : monotone_height sign_lattice.            (* rank = the number of true fields; bound 3 *)
Definition sign_gamma (w : width) (s : sign) (z : Z) : Prop :=
  (signed w z < 0 -> neg s = true) /\ (signed w z = 0 -> zero s = true) /\
  (0 < signed w z -> pos s = true).
Definition sign_domain : word_domain sign.
(* ptop = all true; pconst w z = the sign of signed w z; pmeet = field-wise andb. Rules below. *)
```

Rules of the interval domain (unsigned view; a result that could wrap falls back to `[0, 2^rw -
1]`).
Before applying a rule, meet each operand of width `w` with `ptop w`.
`bvadd bvsub bvmul bvneg`: interval arithmetic, exact when in range. `bvand bvor bvxor bvnot`: from
the
bounds (`min hi` under an and; the next power of two minus one over an or or xor; `2^w - 1 - hi` for
not). Shifts by an amount interval below `w`: shifted bounds when in range. `bvudiv bvurem`: from
the
bounds when the divisor excludes zero, else also all ones (resp. the dividend). Signed operators
other than `bvsrem` and `bvsmod` are exact when every operand lies in one sign half. For `bvsrem`
and `bvsmod`, use sound sign-aware bounds in that case; their result need not be the least interval
hull. For example, 8-bit `[5, 5]` `bvsrem` `[2, 3]` may return `[0, 2]` although the least hull is
`[1, 2]`. The total word semantics, including a zero divisor, remains covered by `word_laws`.
Comparisons: `1` or `0` when decided, else `[0, 1]`.
Extensions, `bvtrunc`, `bvconcat`, `bvite`: bound arithmetic or the join. Counts: `[0, w]`;
rotations:
the whole range. `assume`: a comparison with a known result refines both operands (`bvult` = 1:
`x <= hi_y - 1` and `y >= lo_x + 1`; `bveq` = 1 meets; signed ones when both lie in one half);
`bvadd bvsub bvzext bvtrunc` invert when no wrap is possible; the rest leave operands unchanged.

Rules of the sign domain. Comparisons are decided when the signs decide them. `bvand`: negative only
if both operands are, and not negative if either operand is not. `bvor`: negative if either is.
`bvxor`: negative iff the signs differ. `bvnot`: a negative operand gives `{zero, pos}`, the others
`{neg}`. `bvneg`: negative gives `{neg, pos}` (the minimum maps to itself), positive `{neg}`, zero
`{zero}`. `bvzext`: not negative. `bvsext`: the same sign. `bvite`: the join. Anything else: all
three.

### Known bits (`DomainsKnownBits.v`, DOM-2)

```coq
Record tnum : Type := Tnum { zeros : Z; ones : Z }.     (* a set bit of zeros (ones): that bit is known 0 (1) *)
Definition tnum_lattice (w : width) : lattice tnum.
(* masks are read modulo 2^w. leb a b: everything b knows, a knows (zeros b and ones b are subsets
   of zeros a and ones a); bot = Tnum (2^w - 1) (2^w - 1) (every bit contradictory: no value);
   join: bitwise and of both masks; widen = join; narrow a _ = a *)
Definition tnum_height (w : width) : monotone_height (tnum_lattice w).
(* rank = 2w - popcount zeros - popcount ones over w bits; bound 2w *)
Definition tnum_gamma (w : width) (t : tnum) (z : Z) : Prop :=
  Z.land z (wrap w (zeros t)) = 0 /\ Z.land (wrap w (ones t)) (Z.lnot z) = 0.
Definition known_bits_domain : word_domain tnum.
(* ptop = Tnum 0 0; pconst w c = Tnum (2^w - 1 - c') c' with c' = wrap w c;
   pmeet: bitwise or of both masks *)
```

`pforward` classes. Bitwise operators, `bvite`, extensions, truncation, extract, concat and
constant-amount shifts and rotations: exact, bit by bit. `bvadd bvsub bvneg`: the closed forms of
the
Linux kernel's `tnum_add` and `tnum_sub` (`bvneg` is `tnum_sub` of the constant 0), proved by
induction on
the bit with the carry. `bvmul`: exact when both operands are constants; otherwise the low `tz(x) +
tz(y)`
bits are known 0, where `tz` counts the known-0 low bits, and no other bit is known; there is no
general
multiplication claim. Variable-amount shifts and rotations: the join over the amounts the known bits
allow, using the factored algorithm below. `bvudiv`: the leading zeros of the dividend are kept only
if some bit of the divisor is known 1
(division by zero gives all ones), else Top. `bvurem`: the leading zeros of the dividend are kept.
`bvsdiv bvsmod`: Top. `bvsrem`: Top, except that the sign bit is known 0 when the dividend's sign
bit is
known 0. Counts: the bits above `bitlen w` are zero. Comparisons: decided by the highest known
differing
bit. `passume`: project known result bits back through bitwise operators, shifts, extensions,
truncation
and concatenation; invert `bvadd bvsub` with one known operand; `bveq` = 1 meets; `bvult bvule` use
leading
bits; every refinement is a meet with the old fact.

For a well-formed same-width shift or rotation, let `w` be the positive operand width. Normalize
both masks to `w` bits; if either operand has a contradictory bit, return bottom. Otherwise the
allowed amounts are exactly the `w`-bit words with the amount's known-one bits set, known-zero bits
clear, and all other bits independently selectable. Let `S(k, a)` be the exact constant-amount
transfer for the operator, and `join` the tnum least upper bound. Start with `S(base, a)`, where
`base` is the normalized known-one mask. For each selected unknown amount bit `i`, replace the
accumulator `r` by `join r (S(2^i, r))`. The stages compose shifts by ordinary addition, with
oversized shifts saturating, and rotations by addition modulo `w`. Constant transfers preserve
these joins because every output bit is a copied input bit or a fixed fill bit. Prove this
preservation and the stage invariant; the final fact is the exact join of the constant transfers
over all allowed amounts, hence the best known-bits abstraction of their concrete results. This
claim is specific to these operations, not to every arithmetic transfer.

For shifts, select only unknown bits `i < ceil(log2 w)`. If any unknown higher bit can be set,
also join the oversized result: all zeros for logical shifts, and the dividend sign fill for
arithmetic right shift. The base may itself be oversized; handle that case without constructing
an oversized intermediate integer. For rotations, select every unknown bit below `w`, using
`2^i mod w` as the stage amount; update that residue by doubling modulo `w`. In particular,
non-power-of-two widths cannot discard higher amount bits. The amount is wrapped to `w` bits as
in `eval_op`; rotations reduce it modulo `w`. Widths are positive, so width zero is not a legal
word width. Counts retain the above rule, including the wrapped result of `clz` and `ctz` on zero.
Use binary fuel or a structurally bounded traversal, and prove the oversized and sign-fill cases.

### Wrapping intervals (`DomainsWrapped.v`, DOM-3)

```coq
Inductive wrapped : Type :=
  | WBot
  | WFull
  | WItv (lo hi : Z).
Definition wrapped_size (w : width) (a : wrapped) : Z.      (* the number of words in the arc *)
Definition wrapped_lattice (w : width) : lattice wrapped.
(* WItv lo hi with 0 <= lo, hi < 2^w is the arc lo, lo+1, ..., hi modulo 2^w; it passes through 0
   when lo > hi. An arc of size 2^w is WFull: every operation first normalises (ends read modulo
   2^w, a size-2^w arc becomes WFull). Write off c x = (x - c) mod 2^w. WBot <= everything;
   everything <= WFull; WFull <= only WFull; WItv a b <= WItv c d iff off c a <= off c b <= off c d.
   join a b: WBot is neutral; if leb a b then b; if leb b a then a; otherwise the smaller, by size,
   of the arcs [a.lo, b.hi] and [b.lo, a.hi] that leb-cover both a and b; if neither covers both,
   WFull (after Navas et al.). widen a b: a if leb b a, else join (double a) b, where double
   [lo, hi] is [lo - s, hi + s] with s = size (so of size 3s), or WFull when 3s >= 2^w, and
   double WBot = WBot. narrow a b: b if a is WFull, else a *)
Definition wrapped_wrank (w : width) : bounded_widening_rank (wrapped_lattice w).
(* wrank WBot = wbound = w + 2; WFull 0; WItv lo hi = w + 1 - Z.log2 (wrapped_size w (WItv lo hi)) *)
Definition wrapped_gamma (w : width) (a : wrapped) (z : Z) : Prop :=
  match a with
  | WBot => False
  | WFull => is_word w z
  | WItv lo hi => is_word w z /\ (z - lo) mod modulus w <= (hi - lo) mod modulus w
  end.
Definition wrapped_domain : word_domain wrapped.
(* ptop w = WFull; pconst w z = WItv z' z' with z' = wrap w z. pmeet w a b: WBot absorbs and WFull is
   neutral; for two arcs, WBot when they share no word, the common arc when the intersection is one
   arc, and a otherwise (the intersection is two arcs, a over-approximates it, and a is below no
   arc other than itself, so only the left lower bound pmeet_lower_left holds) *)
```

Rules, after Navas, Schachte, Søndergaard and Stuckey (APLAS 2012): `bvadd bvsub`: `[a,b] + [c,d] =
[a + c, b + d]` unless the sizes add to more than the circle, then `WFull`; `bvneg`: `[-b, -a]`;
`bvmul`:
cut each arc at the north pole (`0 | 2^w - 1`) and the south pole, multiply the unsigned and signed
pieces, keep the smaller arc; divisions and `bvand bvor bvxor`: through the bounds of the pieces;
`bvzext bvsext bvtrunc`: the same arc when it does not cross the relevant pole or fits, else `WFull`
or the joined pieces; comparisons: decided when the arcs are separated; `bvite`: the join; the rest
`WFull`. `assume`: refine by the arcs below or above the other operand for `bvult bvule bvslt
bvsle`,
meet for `bveq`, invert `bvadd bvsub`, project `bvzext bvsext bvtrunc`.

### Congruences (`DomainsCongruence.v`, DOM-4)

```coq
Inductive cong : Type :=
  | CBot
  | Cong (m r : Z).                         (* z = r modulo m; m = 0 means z = r exactly *)
Definition cong_norm (w : width) (c : cong) : cong.
(* reduce r modulo m; a modulus of at least 2^w denotes at most one word: an exact value, or CBot *)
Definition cong_lattice (w : width) : lattice cong.
(* every comparison, join, widen and rank first applies cong_norm w. CBot <= everything;
   Cong m1 r1 <= Cong m2 r2 iff m1 mod m2 = 0 and (r1 - r2) mod m2 = 0 (Rocq's mod by 0 is the
   dividend, so a zero modulus means "exactly"); join: Cong (Z.gcd (Z.gcd m1 m2) (r1 - r2)) r1 with
   CBot neutral, then normalised; widen = join; narrow a _ = a *)
Definition cong_height (w : width) : monotone_height (cong_lattice w).
(* rank CBot = 0; an exact value 1; on a normalised Cong m _ with 1 <= m < 2^w the rank is
   2 + w - Z.log2 m (no Omega: a proper divisor at least halves the modulus); bound w + 2 *)
Definition cong_gamma (w : width) (c : cong) (z : Z) : Prop :=
  match c with CBot => False | Cong m r => is_word w z /\ (z - r) mod m = 0 end.
Definition cong_domain : word_domain cong.
(* ptop w = Cong 1 0; pconst w z = Cong 0 (wrap w z); pmeet: the Chinese-remainder intersection,
   CBot if the residues clash; join, widen and pmeet normalise their arguments first.
   pforward: bvadd bvsub bvneg bvmul: congruence arithmetic, then the modulus is replaced by its gcd
   with 2^w (wrapping preserves only moduli dividing 2^w); constant-amount bvshl: Cong (m * 2^k)
   (r * 2^k) then the same gcd; bvurem by a constant c: modulus gcd m c; bvzext: unchanged; bvtrunc t:
   modulus gcd m 2^t; bvite: join; the rest Cong 1 0 *)
```

### Reduced products (`DomainsProduct.v`, DOM-4)

One functor builds every product; a reduction supplies the extra precision. Product meanings are
explicitly restricted to words at the supplied width. This restriction is local to products:
`payload_concretisation`, `const_gamma` and the other component meanings remain unchanged.

```coq
Definition product_word_domain {P Q} (D1 : word_domain P) (D2 : word_domain Q)
  (reduce : width -> P * Q -> P * Q) : word_domain (P * Q).
(* plat w = reduced_lattice (plat D1 w) (plat D2 w) (reduce w); ptop and pconst: pairs;
   pforward o wps rw = reduce rw (pforward D1 on the first components, pforward D2 on the second);
   passume: both refinements, each refined operand reduced at its width;
   pmeet w a b = reduce w (pmeet D1 w (fst a) (fst b), pmeet D2 w (snd a) (snd b)) *)
Definition product_pgamma {P Q} (G1 : width -> P -> Z -> Prop) (G2 : width -> Q -> Z -> Prop) :
  width -> P * Q -> Z -> Prop :=
  fun w pq z => is_word w z /\ G1 w (fst pq) z /\ G2 w (snd pq) z.
Definition payload_concretisation {P} (G : width -> P -> Z -> Prop) (w : width) : concretisation P Z :=
  {| gamma := G w |}.
Definition word_payload_concretisation {P} (G : width -> P -> Z -> Prop) (w : width) :
  concretisation P Z := {| gamma := fun p z => is_word w z /\ G w p z |}.

(* Every reduction sends a pair with an empty component, one whose leb to its bottom holds, to the
   bottom pair; reduction_empty states it. *)
Definition reduction_empty {P Q} (LP : lattice P) (LQ : lattice Q) (reduce : P * Q -> P * Q) : Prop :=
  forall p q, leb LP p (bot LP) = true \/ leb LQ q (bot LQ) = true -> reduce (p, q) = (bot LP, bot LQ).

Definition reduce_bits_wrapped (w : width) : tnum * wrapped -> tnum * wrapped.
(* Normalize the arc first. A component <= bottom or contradictory known bits gives the bottom pair.
   With WFull, keep the pair unchanged after those checks. With a proper arc, round its end points
   to the nearest values consistent with the known bits in its circular order, returning the bottom
   pair if none exists; then, if the arc does not wrap, make its common leading bits known. Do two
   rounds. Keeping WFull avoids choosing between incomparable arcs when there is no least arc
   containing all the allowed words; it is required for monotonicity with these proper-arc rounds. *)
Definition reduce_interval_cong (w : width) : interval * cong -> interval * cong.
(* an empty component gives the bottom pair; otherwise round lo up and hi down to values congruent to
   r modulo m (Granger 1989); crossing end points give the bottom pair; equal end points make the
   congruence exact and the interval a point *)
Definition reduce_const_with {Q} (D : word_domain Q) (exact : width -> Q -> option Z) (w : width) :
  flat Z * Q -> flat Z * Q.
(* Let B = (FBot, bot (plat D w)) and f c q = pmeet D w q (pconst D w c).
   First return B for FBot or q <= bot. For FVal c, return B if c is not a word; otherwise
   compute q' = f c q, return B if q' <= bot, and return (FVal c, q') otherwise.
   For FTop, query exact w q: None returns (FTop, q); Some c returns (FVal c, q) if c is a word,
   and B otherwise. Test is_word using decidable integer bounds. In the FVal branch do not query
   exact: the mismatch law below makes an exact conflicting payload reduce to B via the meet. *)

(* These are additional caller obligations, not laws of all word domains. All comparisons use the
   payload's preorder; they do not assert that pmeet is a greatest lower bound. *)
Record const_reduction_laws {Q} (D : word_domain Q) (G : width -> Q -> Z -> Prop)
  (exact : width -> Q -> option Z) : Prop := {
  const_exact_sound : forall w q c z, exact w q = Some c -> is_word w z -> G w q z -> z = c;
  const_exact_monotone : forall w q1 q2 c, leb (plat D w) q1 q2 = true ->
    exact w q2 = Some c ->
    leb (plat D w) q1 (bot (plat D w)) = true \/ exact w q1 = Some c;
  const_meet_monotone : forall w c q1 q2, is_word w c ->
    leb (plat D w) q1 q2 = true ->
    leb (plat D w) (pmeet D w q1 (pconst D w c))
      (pmeet D w q2 (pconst D w c)) = true;
  const_meet_idempotent : forall w c q, is_word w c ->
    leb (plat D w) (pmeet D w q (pconst D w c))
      (pmeet D w (pmeet D w q (pconst D w c)) (pconst D w c)) = true;
  const_meet_exact_fixed : forall w c q, is_word w c -> exact w q = Some c ->
    leb (plat D w) q (pmeet D w q (pconst D w c)) = true;
  const_meet_mismatch : forall w c q d, is_word w c -> exact w q = Some d -> c <> d ->
    leb (plat D w) (pmeet D w q (pconst D w c)) (bot (plat D w)) = true
}.

Definition bits_wrapped_domain : word_domain (tnum * wrapped).
Definition interval_cong_domain (thresholds : list Z) : word_domain (interval * cong).
Definition const_product_domain {Q} (D : word_domain Q) (exact : width -> Q -> option Z) :
  word_domain (flat Z * Q).
(* each is product_word_domain with the matching reduction *)
```

### Demanded bits (`DomainsDemanded.v`, DOM-5)

A mask says which bits of a value matter. This is an agreement domain: a mask `m` relates two words
that are equal on the bits of `m`, and `demand` runs a transfer backwards, from the mask of a result
to
the masks of the operands.

```coq
Definition mask_lattice (w : width) : lattice Z.
(* bits at or above w are ignored: leb a b iff Z.land (wrap w a) (Z.lnot (wrap w b)) = 0;
   bot = 0; join = widen = Z.lor; narrow a _ = a *)
Definition mask_height (w : width) : monotone_height (mask_lattice w).    (* rank = popcount (wrap w m); bound w *)
Definition mask_agreement (w : width) : agreement Z word :=
  {| agree := fun m x y =>
       Z.land (wrap w (snd x)) (wrap w m) = Z.land (wrap w (snd y)) (wrap w m) |}.
Definition demand : op -> list width -> list (option Z) -> Z -> list Z.
(* demand o ws consts m: the masks, one per operand, on which operands of widths ws must agree so
   that the result agrees on m. consts holds each operand's value when forward facts know it. *)
Definition agree_masks (ms : list Z) (xs ys : list word) : Prop :=
  Forall2 (fun m p => agree (mask_agreement (fst (fst p))) m (fst p) (snd p)) ms (List.combine xs ys).
Definition consts_hold (consts : list (option Z)) (xs : list word) : Prop :=
  Forall2 (fun co x => forall c, co = Some c -> wrap (fst x) (snd x) = wrap (fst x) c) consts xs.
Definition masks_leb (ws : list width) (ms ms' : list Z) : Prop :=
  Forall2 (fun w p => leb (mask_lattice w) (fst p) (snd p) = true) ws (List.combine ms ms').
```

The rules of `demand`. Every rule starts with `m := wrap rw m`, where `rw` is the result width (bits
at
or above `rw` are ignored). Then, with `fill_down m` all bits at or below the highest bit of `m` (so
carries are covered), `fill_up m` all bits of the operand at or above the lowest bit of `m`, and
`all`
the full mask of an operand: if `m = 0` every operand mask is `0`. `bvand`: `m`, and `m & c` for an
operand whose other operand is the known constant `c`; `bvor`: `m`, and `m & ~c` likewise; `bvxor
bvnot`:
`m`. `bvadd bvsub bvmul bvneg`: `fill_down m` for each operand. `bvshl` by a known `k`: `m >> k` for
the
first operand; `bvlshr`: `m << k`; `bvashr`: `m << k` plus the sign bit `w - 1` iff some bit `i` of
`m` has
`i + k >= w`; the known amount itself needs `0`; a variable amount: `fill_down m` (`bvshl`) or
`fill_up m`
(`bvlshr`, `bvashr`) for the first operand, and `all` for the amount. `bvrotl` by a known `k`: `m`
rotated
right by `k` for the first operand; `bvrotr` by a known `k`: `m` rotated left by `k`; unknown
amount:
`all`. `bvzext`: `m` restricted to the operand's width; `bvsext`: the same plus the sign bit if `m`
has a
bit at or above it; `bvtrunc t`: `m`; `bvextract hi lo`: `m << lo`; `bvconcat`: `m >> w2` for the
high
part and `m` below `w2` for the low part. `bvite`: mask `1` for the condition, `m` for both
branches.
Every other operator (`bvudiv bvurem bvsdiv bvsrem bvsmod`, comparisons, `bvclz bvctz bvpopcnt`):
`all`
for every operand.

### Memory domains (DOM-6)

```coq
(* DomainsAddress.v: where an access happens *)
Record address : Type := Address {
  site : option positive;               (* singleton object; None: unknown or summary site *)
  offset : interval;                    (* byte offset from the base of the object *)
  size : nat                            (* bytes accessed *)
}.
Definition access : Type := (positive * Z * nat)%type.                (* object, byte offset, size *)
Definition bytes_of (c : access) (b : positive * Z) : Prop :=
  fst b = fst (fst c) /\ snd (fst c) <= snd b < snd (fst c) + Z.of_nat (snd c).
Definition address_gamma : concretisation address access.
(* gamma a (s, k, n): n = size a, site a is None or Some s, and k is in offset a *)
(* Some s denotes one concrete object. A summary site is represented by None, so equal summary
   sites never justify the same-object clauses of covers or disjoint. *)
Definition covers (a1 a2 : address) : bool.
(* the site of a1 is known and equals that of a2, the offset of a1 is one finite value k, and every
   offset of a2 lies in [k, k + Z.of_nat (size a1) - Z.of_nat (size a2)] *)
Definition disjoint (a1 a2 : address) : bool.
(* an offset is empty; or both sites are known and differ; or the sites are known and equal, the
   offsets have finite bounds, and hi1 + size a1 <= lo2 or hi2 + size a2 <= lo1 *)
Definition may_overlap (a1 a2 : address) : bool := negb (disjoint a1 a2).

(* DomainsPointsTo.v: what a pointer may point to *)
Definition points_to : Type := (FinSet.t positive * bool)%type.     (* sites, and whether an unknown object is possible *)
Definition points_to_lattice : lattice points_to :=
  product_lattice (powerset_lattice positive_encoding) bool_lattice.
Definition points_to_gamma : concretisation points_to positive.
(* gamma (s, u) p: FinSet.mem positive_encoding p s = true, or u = true *)
Definition pts_of_site (s : positive) : points_to := (FinSet.add positive_encoding s FinSet.empty, false).
Definition pts_unknown : points_to := (FinSet.empty, true).
Definition pts_may_alias (a b : points_to) : bool :=
  snd a || snd b || negb (FinSet.is_empty (FinSet.inter positive_encoding (fst a) (fst b))).
Definition pts_must_alias (a b : points_to) : bool.
(* neither has the unknown flag, and each has exactly one site, the same one *)

(* DomainsByteRange.v: sets of bytes as sorted disjoint half-open ranges *)
Definition range : Type := (Z * Z)%type.                          (* [lo, hi) *)
Definition ranges_wf (rs : list range) : Prop :=
  Forall (fun r => fst r < snd r) rs /\ StronglySorted (fun r1 r2 => snd r1 < fst r2) rs.
Definition byte_ranges : Type := { rs : list range | ranges_wf rs }.   (* canonical: no empty or adjacent ranges *)
Definition ranges_empty : byte_ranges.
Definition ranges_mem (rs : byte_ranges) (b : Z) : bool.
Definition ranges_add (r : range) (rs : byte_ranges) : byte_ranges.       (* an empty r changes nothing *)
Definition ranges_remove (r : range) (rs : byte_ranges) : byte_ranges.
Definition ranges_union (rs1 rs2 : byte_ranges) : byte_ranges.
Definition ranges_inter (rs1 rs2 : byte_ranges) : byte_ranges.
Definition ranges_diff (rs1 rs2 : byte_ranges) : byte_ranges.
Definition ranges_covers (rs : byte_ranges) (r : range) : bool.           (* every byte of r is in rs *)
Definition ranges_intersects (rs : byte_ranges) (r : range) : bool.       (* some byte of r is in rs *)
Definition ranges_lattice : lattice byte_ranges.                           (* may: inclusion; join = union *)
Definition ranges_gamma : concretisation byte_ranges Z.                    (* gamma rs b: ranges_mem rs b = true *)
```

```coq
(* DomainsFootprint.v: byte ranges of allocation sites; T is the site type (DOM-6) *)
Record footprint (T : Type) : Type := Footprint { fp_site : T; fp_lo : Z; fp_hi : Z }.
(* the bytes [fp_lo, fp_hi) of every block allocated at fp_site *)
Definition covered {T} (F : list (footprint T)) (t : T) (o : Z) (w : nat) : Prop :=
  forall k, (o <= k < o + Z.of_nat w)%Z ->
    exists f, In f F /\ fp_site f = t /\ (fp_lo f <= k < fp_hi f)%Z.
(* every byte of the access lies in a footprint; zero bytes are always covered *)
Definition written {T} (F : list (footprint T)) (t : T) (k : Z) : Prop :=
  exists f, In f F /\ fp_site f = t /\ (fp_lo f <= k)%Z /\ (k < fp_hi f)%Z.     (* byte k of site t *)
Definition footprint_encoding {T} (ET : encoding T) : encoding (footprint T).
(* encode f = encode (pair_encoding ET (pair_encoding Z_encoding Z_encoding)) (fp_site f, (fp_lo f, fp_hi f)) *)
Definition footprints_canonical {T} (ET : encoding T) (F : list (footprint T)) : Prop :=
  Forall (fun f => (fp_lo f < fp_hi f)%Z) F /\
  StronglySorted (fun f g => (encode ET (fp_site f) < encode ET (fp_site g))%positive \/
    (fp_site f = fp_site g /\ (fp_hi f < fp_lo g)%Z)) F.
(* canonical: sites in increasing code; per site the ranges are sorted, disjoint, non-adjacent and
   non-empty, exactly the byte_ranges of that site (site_ranges below) *)
Definition site_ranges {T} (ET : encoding T) (F : list (footprint T)) (t : T) : list range.
(* the (fp_lo, fp_hi) of the footprints of site t, in list order *)
Definition footprints_normalise {T} (ET : encoding T) (F : list (footprint T)) : list (footprint T).
Definition footprints_inter {T} (ET : encoding T) (F G : list (footprint T)) : list (footprint T).
Definition footprints_diff {T} (ET : encoding T) (F G : list (footprint T)) : list (footprint T).
(* Preparation buckets ranges by site, then filters, sorts and coalesces each bucket once, with a
   separate sort of occupied site codes. Inter and diff combine the prepared indexes using the public
   byte_ranges operations; the results are canonical. *)

(* The must-facts of written bytes. The reached carrier contains only canonical lists. *)
Definition canonical_footprints {T} (ET : encoding T) : Type :=
  { F : list (footprint T) | footprints_canonical ET F }.
Definition range_must {T} (ET : encoding T) : Type := lift_bot (canonical_footprints ET).
Definition range_reached {T} (ET : encoding T) (F : list (footprint T)) : range_must ET.
(* Reached (footprints_normalise ET F), with its canonicality proof *)
Definition range_written {T} {ET : encoding T} (a : range_must ET) (t : T) (k : Z) : Prop :=
  match a with Unreached => True | Reached F => written (proj1_sig F) t k end.
Definition range_must_lattice {T} (ET : encoding T) : lattice (range_must ET).
(* reverse coverage order: leb Unreached _ = true; leb (Reached F) Unreached = false; leb (Reached F)
   (Reached G): every byte of proj1_sig G is a byte of proj1_sig F (decided on normal forms);
   bot = Unreached; join: Unreached is neutral; two Reached values give range_reached ET
   (footprints_inter ET (proj1_sig F) (proj1_sig G));
   widen = join; narrow a _ = a. leb, join, range_add and range_remove normalise their list inputs;
   per-site work reuses byte_ranges operations. *)
Definition range_must_top {T} (ET : encoding T) : top (range_must_lattice ET). (* range_reached ET nil *)
Definition range_add {T} (ET : encoding T) (fs : list (footprint T))
  (a : range_must ET) : range_must ET.
(* Unreached stays; Reached F gives range_reached ET (fs ++ proj1_sig F) *)
Definition range_remove {T} (ET : encoding T) (fs : list (footprint T))
  (a : range_must ET) : range_must ET.
(* Unreached stays; Reached F removes every byte that fs overlaps, then normalises. *)
Definition range_covers {T} {ET : encoding T} (a : range_must ET) (t : T) (o : Z) (w : nat) : Prop :=
  forall k, (o <= k < o + Z.of_nat w)%Z -> range_written a t k.
Definition range_must_gamma {T} {ET : encoding T} : concretisation (range_must ET) (T -> Z -> Prop).
(* Unreached: nothing; Reached F: the sets W of written bytes with W (fp_site f) k for every f in
   proj1_sig F and every k in [fp_lo f, fp_hi f) *)
```

### Equality partitions (`DomainsEquality.v`, DOM-7)

A fact "these keys are equal" is a partition of the keys; the join of two facts keeps the equalities
that hold in both, which is the intersection of the two equivalence relations.

```coq
Definition partition {K} (E : encoding K) : Type := lift_bot { u : UnionFind.t K | UnionFind.wf E u }.
(* Unreached: unreachable, every key equal to every other (the bottom) *)
Definition partition_equiv {K} (E : encoding K) (p : partition E) (x y : K) : Prop :=
  match p with Unreached => True | Reached u => UnionFind.equiv E (proj1_sig u) x y end.
Definition partition_lattice {K} (E : encoding K) : lattice (partition E).
(* leb Unreached _ = true; leb (Reached _) Unreached = false; leb (Reached u1) (Reached u2): every
   equality of u2 holds in u1; bot = Unreached; join Unreached p = p; join (Reached u1) (Reached u2)
   is Reached with the intersection of the
   equivalences (the keys of both supports grouped by the pair of their representatives);
   widen = join; narrow a _ = a *)
Definition partition_top {K} (E : encoding K) : top (partition_lattice E).  (* Reached UnionFind.make *)
Definition partition_union {K} (E : encoding K) (x y : K) (p : partition E) : partition E.   (* add x = y *)
Definition partition_forget {K} (E : encoding K) (x : K) (p : partition E) : partition E.
(* Unreached stays Unreached. Reached u: x's class is rebuilt without x and x becomes alone: the
   structure with the classes of u on the support keys other than x, e.g. each such key unioned with
   the first key of its class in u (x itself is skipped even when it is the representative) *)
Definition key_update {K V} (E : encoding K) (x : K) (v : V) (s : K -> V) : K -> V :=
  fun k => if Pos.eqb (encode E k) (encode E x) then v else s k.     (* s with x rebound to v *)
Definition partition_test {K} (E : encoding K) (x y : K) (p : partition E) : bool * partition E.
(* the test, and the structure with its paths compressed *)
Definition partition_gamma {K V} (E : encoding K) : concretisation (partition E) (K -> V).
(* Unreached: nothing; Reached u: values of equivalent keys are equal *)

(* DomainsSymbolic.v: symbolic keys for value numbering *)
Definition sym_key : Type := list positive.
Definition expr_key (o : op) (args : list positive) : sym_key.
(* encode op_encoding o, then args; for a commutative o the args are sorted by Pos.compare *)
Record numbering : Type := Numbering { ids : Table.t positive; next : positive }.
Definition numbering_empty : numbering := Numbering Table.empty 1%positive.
Definition intern (k : sym_key) (n : numbering) : positive * numbering.
(* the number of k if it is present; else next n, recorded, with next incremented *)
Definition numbering_wf (n : numbering) : Prop :=
  Table.wf (ids n) /\ (forall k i, Table.get k (ids n) = Some i -> (i < next n)%positive) /\
  (forall k1 k2 i, Table.get k1 (ids n) = Some i -> Table.get k2 (ids n) = Some i -> k1 = k2).
```

## Theorems

### The interface and the width tags (DOM-1a)

```coq
Section NumericLaws.
Context {A : Type} (D : numeric_domain A) (G : concretisation A word) (env : nat -> A)
  (cenv : nat -> word) (e : expr) (a : A) (r : word) (o : op) (args : list expr) (i : nat) (w : width) (z : Z).

(** The abstract evaluator follows the expression's structure. *)
Theorem abs_eval_var : abs_eval D env (Var i) = env i.
Theorem abs_eval_const : abs_eval D env (Const w z) = of_const D w z.
Theorem abs_eval_app : abs_eval D env (App o args) = forward D o (List.map (abs_eval D env) args).
(* Proof idea: unfolding the inner fix. Card: DOM-1a. *)

(** One generic soundness theorem: abstract evaluation over-approximates concrete evaluation. *)
Theorem abs_eval_sound : numeric_laws D G -> env_ok cenv -> env_sound G env cenv ->
  eval cenv e = Some r -> gamma G (abs_eval D env e) r.
(* Proof idea: induction on e; the App case uses forward_sound on the pointwise-sound arguments,
   with the nested induction over args as an auxiliary lemma. Card: DOM-1a. *)

(** A guard keeps the environment sound, and refinement only goes down. *)
Theorem abs_assume_sound : numeric_laws D G -> env_ok cenv -> env_sound G env cenv ->
  eval cenv e = Some r -> gamma G a r -> env_sound G (abs_assume D env e a) cenv.
Theorem abs_assume_refines : numeric_laws D G ->
  leb (lat D) (abs_assume D env e a i) (env i) = true.
(* Proof idea: Var uses meet_sound and meet_lower_left; App uses assume_sound and assume_refines,
   threading the environment through the arguments. Card: DOM-1a. *)
End NumericLaws.

Section TaggedLaws.
Context {P : Type} (D : word_domain P) (G : width -> P -> Z -> Prop).

(** The tagged lattice is a lattice, and a payload domain lifts to a numeric domain. *)
Theorem tagged_laws : (forall w, lattice_laws (plat D w)) ->
  lattice_laws (tagged_lattice (plat D)).
Theorem capped_laws : (forall w, lattice_laws (plat D w)) -> forall maxw : width,
  lattice_laws (capped_lattice maxw (plat D)).
Theorem tagged_numeric_laws : word_laws D G ->
  numeric_laws (tagged_domain D) (tagged_gamma G).
(** Clamping to the cap only widens, and the capped domain is a sound numeric domain. *)
Theorem clamp_gamma : forall (maxw : width) (t : tagged P) (c : word),
  gamma (tagged_gamma G) t c -> gamma (capped_gamma G maxw) (clamp maxw t) c.
Theorem capped_numeric_laws : word_laws D G -> forall maxw : width,
  numeric_laws (capped_domain D maxw) (capped_gamma G maxw).
(* Proof idea: case analysis on TBot, TVal and TAny; Forall2 over the operands turns a list of tags
   into a list of payloads, and eval_op_width (Bits) gives the result width; a payload that is
   <= bot has an empty meaning (pgamma_bot_empty with pgamma_monotone), so returning TBot loses
   nothing; the capped case is the tagged one followed by clamp_gamma. Card: DOM-1a. *)
End TaggedLaws.
```

### Constants and signs (DOM-1a)

```coq
(** Constants and signs: sound payload domains; signs also have least upper bounds. *)
Theorem const_word_laws : word_laws const_domain const_gamma.
Theorem sign_laws : lattice_laws sign_lattice.
Theorem sign_lub : lub_laws sign_lattice.
Theorem sign_word_laws : word_laws sign_domain sign_gamma.
(* Proof idea: the lattice laws by case analysis on the constructors; each transfer rule by
   Bits lemmas (wrap_*, signed_range, testbit laws) for the operator it covers; the constant
   passume rules by inverting the operator with eval_op. Card: DOM-1a. *)
```

### Intervals (DOM-1b)

```coq
Section IntervalLaws.
Context (thresholds : list Z).

(** Intervals: a lattice with least upper bounds, monotone meaning, sound transfers. *)
Theorem interval_laws : lattice_laws (interval_lattice thresholds).
Theorem interval_lub : lub_laws (interval_lattice thresholds).
Theorem interval_gamma_laws : concretisation_laws (interval_lattice thresholds) interval_gamma.
Theorem interval_gamma_bot_empty : bottom_empty (interval_lattice thresholds) interval_gamma.
Theorem interval_word_laws : word_laws (interval_domain thresholds) interval_pgamma.
(* Proof idea: the lattice laws by case analysis on the bounds; each transfer rule by Bits
   lemmas (wrap_*, signed_range, testbit laws) for the operator it covers; assume by inverting
   the operator's rule on the interval bounds. Card: DOM-1b. *)
End IntervalLaws.
```

### Known bits, wrapping intervals, congruences (DOM-2, DOM-3, DOM-4)

```coq
Section WordInstanceLaws.
Context (w : width).

(** Known bits (DOM-2): least upper bounds, and every forward transfer and assume is sound. *)
Theorem tnum_laws : lattice_laws (tnum_lattice w).
Theorem tnum_lub : lub_laws (tnum_lattice w).
Theorem known_bits_word_laws : word_laws known_bits_domain tnum_gamma.
(* Proof idea: bit by bit with testbit_* for the exact operators; the add and sub closed forms
   by induction on the bit with the carry; mul by the trailing zeros of the factors (wmul with
   powers of two); the division rules from wudiv_spec, wurem_lt and the SMT-LIB definitions at a
   zero divisor. Card: DOM-2. *)

(** Wrapping intervals (DOM-3): the join above is an upper bound of minimal size among the covering
    arcs; there is no least upper bound in general, so there is no lub_laws theorem. *)
Theorem wrapped_laws : lattice_laws (wrapped_lattice w).
Theorem wrapped_join_minimal : forall a b c : wrapped,
  leb (wrapped_lattice w) a c = true -> leb (wrapped_lattice w) b c = true ->
  wrapped_size w (join (wrapped_lattice w) a b) <= wrapped_size w c.
Theorem wrapped_gamma_laws : concretisation_laws (wrapped_lattice w)
  (Concretisation wrapped Z (wrapped_gamma w)).
Theorem wrapped_word_laws : word_laws wrapped_domain wrapped_gamma.
(* Proof idea: arcs through off c x = (x - c) mod 2^w; a proper arc c that covers a and b is an
   interval of its own linear order, so one of the two candidate arcs lies inside it
   (wrapped_join_minimal); the widening rank drops because 3s >= 2s raises Z.log2 of the size by
   one; the transfer rules by case analysis on the poles, as in Navas et al. Card: DOM-3. *)

(** Congruences (DOM-4). *)
Theorem cong_laws : lattice_laws (cong_lattice w).
Theorem cong_lub : lub_laws (cong_lattice w).
Theorem cong_word_laws : word_laws cong_domain cong_gamma.
(* Proof idea: divisibility and Z.gcd lemmas; wrapping keeps only moduli dividing 2^w. Card: DOM-4. *)
End WordInstanceLaws.
```

### Reduced products (DOM-4)

```coq
Section ProductWordLaws.
Context {P Q : Type} (D1 : word_domain P) (D2 : word_domain Q) (G1 : width -> P -> Z -> Prop)
  (G2 : width -> Q -> Z -> Prop) (reduce : width -> P * Q -> P * Q).

(** A product of two sound payload domains with a sound, monotone, idempotent reduction is sound. *)
Theorem product_word_laws : word_laws D1 G1 -> word_laws D2 G2 ->
  (forall w, reduction_laws (plat D1 w) (plat D2 w) (reduce w)) ->
  (forall w, reduction_sound (word_payload_concretisation G1 w)
    (word_payload_concretisation G2 w) (reduce w)) ->
  word_laws (product_word_domain D1 D2 reduce) (product_pgamma G1 G2).
(* Proof idea: Order's reduced_laws and reduced_gamma_laws per width; each transfer is the pair of
   transfers followed by reduce, and reduce_gamma keeps the word meaning. `eval_op_is_word` supplies
   the forward result's range; input and assumed operand words already have that range. Card: DOM-4. *)
End ProductWordLaws.

(** Adding the local word restriction does not change any tagged product meaning. *)
Theorem product_tagged_gamma_equiv : forall {P Q : Type}
  (G1 : width -> P -> Z -> Prop) (G2 : width -> Q -> Z -> Prop) a v,
  gamma (tagged_gamma (product_pgamma G1 G2)) a v <->
  gamma (tagged_gamma (fun w pq z => G1 w (fst pq) z /\ G2 w (snd pq) z)) a v.
(* `tagged_gamma` already restricts TVal payloads to words; TBot and TAny are unchanged. Card: DOM-4. *)

Section ReductionLaws.
Context (thresholds : list Z) (w : width).

(** The three reductions only go down, are monotone and idempotent, keep the meaning, and send a
    pair with an empty component to the bottom pair. *)
Theorem reduce_bits_wrapped_laws :
  reduction_laws (tnum_lattice w) (wrapped_lattice w) (reduce_bits_wrapped w) /\
  reduction_sound (word_payload_concretisation tnum_gamma w)
    (word_payload_concretisation wrapped_gamma w)
    (reduce_bits_wrapped w) /\
  reduction_empty (tnum_lattice w) (wrapped_lattice w) (reduce_bits_wrapped w).
Theorem reduce_interval_cong_laws :
  reduction_laws (interval_lattice thresholds) (cong_lattice w) (reduce_interval_cong w) /\
  reduction_sound (word_payload_concretisation interval_pgamma w)
    (word_payload_concretisation cong_gamma w)
    (reduce_interval_cong w) /\
  reduction_empty (interval_lattice thresholds) (cong_lattice w) (reduce_interval_cong w).
Theorem reduce_const_with_laws : forall {Q : Type} (D : word_domain Q) (G : width -> Q -> Z -> Prop)
  (exact : width -> Q -> option Z), word_laws D G -> const_reduction_laws D G exact ->
  reduction_laws (flat_lattice Z.eqb) (plat D w) (reduce_const_with D exact w) /\
  reduction_sound (word_payload_concretisation const_gamma w) (word_payload_concretisation G w)
    (reduce_const_with D exact w) /\
  reduction_empty (flat_lattice Z.eqb) (plat D w) (reduce_const_with D exact w).
(* Proof idea: for proper wrapped arcs use the upper arc's circular linear order: every contained
   proper arc is a subinterval, and intersecting with more known bits only moves selected endpoints
   inward. If the upper rounded arc is nonwrapping, a contained nonempty arc is nonwrapping too,
   so its leading-bit refinement includes the upper one's. Full arcs and contradictions are separate
   cases. Prove one-round monotonicity and that two rounds are stable, including raw masks and arc
   representations. For intervals, the least and greatest consistent endpoints are monotone.
   For constants use the separate meet and exact-query laws, including noncanonical and empty
   payloads. A second application is equivalent in the preorder; soundness keeps every shared word.
   Card: DOM-4. *)
End ReductionLaws.

(** The three named products are sound numeric domains. *)
Theorem bits_wrapped_numeric_laws : numeric_laws (tagged_domain bits_wrapped_domain)
  (tagged_gamma (product_pgamma tnum_gamma wrapped_gamma)).
Theorem interval_cong_numeric_laws : forall thresholds : list Z,
  numeric_laws (tagged_domain (interval_cong_domain thresholds))
    (tagged_gamma (product_pgamma interval_pgamma cong_gamma)).
(* Proof idea: product_word_laws with the reductions' laws, then tagged_numeric_laws. Card: DOM-4. *)
```

### Demanded bits (DOM-5)

```coq
Section DemandedLaws.
Context (w : width) (o : op) (ws : list width) (consts : list (option Z)) (m m' : Z)
  (xs ys : list word) (r1 r2 : word) (rw : width).

(** Masks form a lattice with least upper bounds, and agree-on-the-mask is an agreement. *)
Theorem mask_laws : lattice_laws (mask_lattice w).
Theorem mask_lub : lub_laws (mask_lattice w).
Theorem mask_agreement_laws : agreement_laws (mask_lattice w) (mask_agreement w).
Theorem mask_agreement_bot : agreement_bot (mask_lattice w) (mask_agreement w).
Theorem mask_agreement_join : agreement_join_law (mask_lattice w) (mask_agreement w).
Theorem mask_agreement_equivalence : agreement_equivalence (mask_agreement w).
(* Proof idea: Z.land with Z.lnot and Z.lor; bits below w only, by testbit_wrap. Card: DOM-5. *)

(** Soundness: operands of equal widths that agree under the demanded masks, and whose known
    constants are right, give results that agree under the output mask. *)
Theorem demand_sound : List.map fst xs = List.map fst ys ->
  consts_hold consts xs -> consts_hold consts ys ->
  agree_masks (demand o (List.map fst xs) consts m) xs ys ->
  eval_op o xs = Some r1 -> eval_op o ys = Some r2 ->
  agree (mask_agreement (fst r1)) m r1 r2.
(* Proof idea: per operator, from testbit_* laws: a result bit depends on the operand bits the
   rule demands (carries on bits at or below it). Card: DOM-5. *)

(** Demanding nothing demands nothing, the masks have the arity's length, and demand is monotone. *)
Theorem demand_zero : List.length ws = arity o ->
  demand o ws consts 0 = List.repeat 0 (arity o).
Theorem demand_length : List.length ws = arity o ->
  List.length (demand o ws consts m) = arity o.
Theorem demand_monotone : result_width o ws = Some rw -> leb (mask_lattice rw) m m' = true ->
  masks_leb ws (demand o ws consts m) (demand o ws consts m').
(* Proof idea: each rule is monotone in m (shifts, masks and fill_down preserve inclusion). Card: DOM-5. *)
End DemandedLaws.
```

### Memory domains (DOM-6)

```coq
Section MemoryLaws.
Context (a1 a2 : address) (c1 c2 : access) (b : positive * Z) (s s1 s2 : positive) (k : Z)
  (p q : positive) (pa pb : points_to).

(** Each predicate is sound for every pair of concrete accesses the addresses describe. *)
Theorem covers_sound : covers a1 a2 = true -> gamma address_gamma a1 c1 ->
  gamma address_gamma a2 c2 -> bytes_of c2 b -> bytes_of c1 b.
Theorem disjoint_sound : disjoint a1 a2 = true -> gamma address_gamma a1 c1 ->
  gamma address_gamma a2 c2 -> bytes_of c1 b -> bytes_of c2 b -> False.
Theorem may_overlap_sound : gamma address_gamma a1 c1 -> gamma address_gamma a2 c2 ->
  bytes_of c1 b -> bytes_of c2 b -> may_overlap a1 a2 = true.
(** The predicates are not trivially false: an exact address covers itself, and objects at
    different known sites are disjoint. *)
Theorem covers_exact : site a1 = Some s -> offset a1 = Itv (Fin k) (Fin k) -> covers a1 a1 = true.
Theorem disjoint_sites : site a1 = Some s1 -> site a2 = Some s2 -> s1 <> s2 -> disjoint a1 a2 = true.
(* Proof idea: unfold bytes_of and address_gamma; the offset arithmetic by lia. Card: DOM-6. *)

(** Points-to sets: a lattice with least upper bounds, a monotone meaning, sound alias queries. *)
Theorem points_to_laws : lattice_laws points_to_lattice.
Theorem points_to_lub : lub_laws points_to_lattice.
Theorem points_to_gamma_laws : concretisation_laws points_to_lattice points_to_gamma.
Theorem pts_may_alias_sound : gamma points_to_gamma pa p -> gamma points_to_gamma pb p ->
  pts_may_alias pa pb = true.
Theorem pts_must_alias_sound : pts_must_alias pa pb = true -> gamma points_to_gamma pa p ->
  gamma points_to_gamma pb q -> p = q.
Theorem pts_of_site_gamma : gamma points_to_gamma (pts_of_site s) p <-> p = s.
(* Proof idea: Order's product_laws, powerset_laws and bool_laws; the queries by FinSet.mem_inter. Card: DOM-6. *)
End MemoryLaws.

Section ByteRangeLaws.
Context (rs rs1 rs2 : byte_ranges) (r : range) (b : Z).

(** Membership laws; a byte-range set is determined by its bytes, so equality is extensional. *)
Theorem ranges_mem_empty : ranges_mem ranges_empty b = false.
Theorem ranges_mem_add : ranges_mem (ranges_add r rs) b =
  ((fst r <=? b) && (b <? snd r) || ranges_mem rs b)%bool.
Theorem ranges_mem_remove : ranges_mem (ranges_remove r rs) b =
  (ranges_mem rs b && negb ((fst r <=? b) && (b <? snd r)))%bool.
Theorem ranges_mem_union : ranges_mem (ranges_union rs1 rs2) b = (ranges_mem rs1 b || ranges_mem rs2 b)%bool.
Theorem ranges_mem_inter : ranges_mem (ranges_inter rs1 rs2) b = (ranges_mem rs1 b && ranges_mem rs2 b)%bool.
Theorem ranges_mem_diff : ranges_mem (ranges_diff rs1 rs2) b = (ranges_mem rs1 b && negb (ranges_mem rs2 b))%bool.
Theorem ranges_ext : (forall b, ranges_mem rs1 b = ranges_mem rs2 b) -> proj1_sig rs1 = proj1_sig rs2.
Theorem ranges_covers_spec : ranges_covers rs r = true <->
  forall b, fst r <= b < snd r -> ranges_mem rs b = true.
Theorem ranges_intersects_spec : ranges_intersects rs r = true <->
  exists b, fst r <= b < snd r /\ ranges_mem rs b = true.
(* Proof idea: a linear merge of two sorted lists; the invariant ranges_wf makes neighbours
   non-adjacent, so a canonical list is a function of its bytes. Card: DOM-6. *)

(** The may lattice of byte ranges. *)
Theorem ranges_laws : lattice_laws ranges_lattice.
Theorem ranges_lub : lub_laws ranges_lattice.
Theorem ranges_gamma_laws : concretisation_laws ranges_lattice ranges_gamma.
(* Proof idea: from the membership laws and ranges_ext. Card: DOM-6. *)
End ByteRangeLaws.

Section FootprintLaws.
Context {T : Type} (ET : encoding T) (a b : range_must ET) (F G fs : list (footprint T)) (t : T)
  (o k : Z) (w : nat) (W : T -> Z -> Prop).

(** Normalising keeps the bytes and yields a canonical list; a canonical list is a function of its
    bytes; its per-site ranges are byte_ranges. *)
Theorem footprints_normalise_canonical : footprints_canonical ET (footprints_normalise ET F).
Theorem footprints_normalise_written : written (footprints_normalise ET F) t k <-> written F t k.
Theorem footprints_inter_canonical : footprints_canonical ET (footprints_inter ET F G).
Theorem footprints_inter_written : written (footprints_inter ET F G) t k <->
  written F t k /\ written G t k.
Theorem footprints_diff_canonical : footprints_canonical ET (footprints_diff ET F G).
Theorem footprints_diff_written : written (footprints_diff ET F G) t k <->
  written F t k /\ ~ written G t k.
Theorem footprints_ext : footprints_canonical ET F -> footprints_canonical ET G ->
  (forall t k, written F t k <-> written G t k) -> F = G.
Theorem footprints_canonical_ranges : footprints_canonical ET F -> ranges_wf (site_ranges ET F t).
(* Proof idea: the per-site claims are the ByteRangeLaws on site_ranges; the sort by encode
   orders the sites. Card: DOM-6. *)

(** covered is exactly bytewise coverage, including empty accesses and noncanonical lists. *)
Theorem covered_written : covered F t o w -> forall k, o <= k < o + Z.of_nat w -> written F t k.
Theorem covered_bytewise :
  (covered F t o w <-> forall k, o <= k < o + Z.of_nat w -> written F t k).
(* Proof idea: unfold covered and written. Card: DOM-6. *)

(** The must lattice of ranges: a lattice with least upper bounds, ordered by bytes. *)
Theorem range_must_laws : lattice_laws (range_must_lattice ET).
Theorem range_must_lub : lub_laws (range_must_lattice ET).
Theorem range_must_leb_spec : leb (range_must_lattice ET) (range_reached ET F)
  (range_reached ET G) = true <->
  forall t k, written G t k -> written F t k.
Theorem range_reached_written : range_written (range_reached ET F) t k <-> written F t k.
(** Meaning: Unreached has no concrete states; Reached F means every footprint byte is written. *)
Theorem range_must_gamma_laws : concretisation_laws (range_must_lattice ET) range_must_gamma.
Theorem range_must_gamma_bot_empty : bottom_empty (range_must_lattice ET) range_must_gamma.
Theorem range_must_gamma_top_full : top_full (range_must_top ET) range_must_gamma.
Theorem range_covers_sound : gamma range_must_gamma a W -> range_covers a t o w ->
  forall k, o <= k < o + Z.of_nat w -> W t k.
(** range_covers is exactly bytewise coverage, including an access of zero bytes. *)
Theorem range_covers_iff_written :
  (range_covers a t o w <-> forall k, o <= k < o + Z.of_nat w -> range_written a t k).
(** Coverage lemmas: adding makes the added bytes covered and keeps the old ones; removing takes the
    overlapped bytes away and keeps the others. *)
Theorem range_covers_add :
  (range_covers (range_add ET fs a) t o w <->
   forall k, o <= k < o + Z.of_nat w -> written fs t k \/ range_written a t k).
Theorem range_covers_remove :
  (range_covers (range_remove ET fs (range_reached ET F)) t o w <->
   forall k, o <= k < o + Z.of_nat w -> written F t k /\ ~ written fs t k).
(** The operations are sound for the meaning: added bytes that are written stay written, and bytes
    outside fs keep their status when fs may have been overwritten. *)
Theorem range_add_gamma : gamma range_must_gamma a W ->
  (forall f k, In f fs -> fp_lo f <= k < fp_hi f -> W (fp_site f) k) ->
  gamma range_must_gamma (range_add ET fs a) W.
Theorem range_remove_gamma : forall W' : T -> Z -> Prop, gamma range_must_gamma a W ->
  (forall t k, ~ written fs t k -> W t k -> W' t k) ->
  gamma range_must_gamma (range_remove ET fs a) W'.
(* Proof idea: bytes of the results by the footprints_*_written laws; the order is reverse byte
   inclusion, so reflexivity, transitivity and the upper bounds are propositional; join_least follows
   from intersection. Card: DOM-6. *)
End FootprintLaws.

(** footprint_encoding is the encoding of the triple of site code and bounds, by construction. *)
Theorem footprint_encoding_spec : forall {T} (ET : encoding T) (f : footprint T),
  encode (footprint_encoding ET) f =
  encode (pair_encoding ET (pair_encoding Z_encoding Z_encoding)) (fp_site f, (fp_lo f, fp_hi f)).
(* Proof idea: unfolding the definition; injectivity comes from the pair encoding's. Card: DOM-6. *)
```

### Equality partitions and symbolic keys (DOM-7)

```coq
Section PartitionLaws.
Context {K V : Type} (E : encoding K) (x y a b : K) (p p1 p2 : partition E) (s : K -> V) (v : V).

(** Partitions form a lattice with least upper bounds; the join is the intersection of equivalences. *)
Theorem partition_laws : lattice_laws (partition_lattice E).
Theorem partition_lub : lub_laws (partition_lattice E).
Theorem partition_join_spec : partition_equiv E (join (partition_lattice E) p1 p2) a b <->
  partition_equiv E p1 a b /\ partition_equiv E p2 a b.
(** Adding an equality merges exactly the two classes. *)
Theorem partition_union_spec : partition_equiv E (partition_union E x y p) a b <->
  partition_equiv E p a b \/
  (partition_equiv E p a x /\ partition_equiv E p y b) \/
  (partition_equiv E p a y /\ partition_equiv E p x b).
(** Forgetting x: it leaves its class, the other equalities stay, and only equalities are lost. The
    specification needs p <> Unreached, whose equivalence relates every pair. *)
Theorem partition_forget_unreached : partition_forget E x Unreached = Unreached.
Theorem partition_forget_spec : p <> Unreached ->
  (partition_equiv E (partition_forget E x p) a b <->
   (partition_equiv E p a b /\ a <> x /\ b <> x) \/ (a = x /\ b = x)).
Theorem partition_forget_leb : leb (partition_lattice E) p (partition_forget E x p) = true.
Theorem partition_forget_gamma : gamma (@partition_gamma K V E) p s ->
  gamma (@partition_gamma K V E) (partition_forget E x p) (key_update E x v s).
(** The test agrees with the relation and returns an equivalent partition. *)
Theorem partition_test_correct :
  (fst (partition_test E x y p) = true <-> partition_equiv E p x y) /\
  (forall a b, partition_equiv E (snd (partition_test E x y p)) a b <-> partition_equiv E p a b).
(** Meaning: equal keys hold equal values; the bottom denotes nothing; the top everything. *)
Theorem partition_gamma_laws : concretisation_laws (partition_lattice E) (@partition_gamma K V E).
Theorem partition_gamma_bot_empty : bottom_empty (partition_lattice E) (@partition_gamma K V E).
Theorem partition_top_full : top_full (partition_top E) (@partition_gamma K V E).
(* Proof idea: UnionFind.union_equiv, equivb_correct and keys_support; the join groups keys by the
   pair of representatives, which is the meet of the two equivalences; forget unions the support
   keys other than x with their first classmate, so classes of u lose only x (keys_support for keys
   outside the support), and the gamma law reads the specification at a and b. Card: DOM-7. *)
End PartitionLaws.

Section SymbolicLaws.
Context (n : numbering) (k k1 k2 k' : sym_key) (i : positive) (o : op) (args1 args2 : list positive)
  (a b : positive).

(** Interning: found keys keep their number, new keys get the next one, and the table only grows. *)
Theorem numbering_wf_empty : numbering_wf numbering_empty.
Theorem numbering_wf_intern : numbering_wf n -> numbering_wf (snd (intern k n)).
Theorem intern_get : Table.get k (ids (snd (intern k n))) = Some (fst (intern k n)).
Theorem intern_found : Table.get k (ids n) = Some i -> intern k n = (i, n).
Theorem intern_fresh : Table.get k (ids n) = None ->
  fst (intern k n) = next n /\ next (snd (intern k n)) = Pos.succ (next n).
Theorem intern_stable : Table.get k' (ids n) = Some i -> Table.get k' (ids (snd (intern k n))) = Some i.
(** Numbers identify keys: two keys that get one number from a threaded numbering are equal. *)
Theorem intern_injective : numbering_wf n ->
  fst (intern k2 (snd (intern k1 n))) = fst (intern k1 n) -> k2 = k1.
(** Keys respect commutativity, and equal keys denote equal values under any valuation. *)
Theorem expr_key_commutative : commutative o = true -> expr_key o [a; b] = expr_key o [b; a].
Theorem expr_key_eval : expr_key o args1 = expr_key o args2 -> forall val : positive -> word,
  eval_op o (List.map val args1) = eval_op o (List.map val args2).
(* Proof idea: Table.get_set_* and Table.wf_set; expr_key_eval by cases on commutative, using
   commutative_sound when the sorted lists are equal but the lists differ. Card: DOM-7. *)
End SymbolicLaws.
```

## Algorithms and references

- **Abstract domains.** P. Cousot and R. Cousot, POPL 1977 and 1979: lattices, widening, narrowing,
  reduced products, signs. Constants: Kildall, POPL 1973. Intervals with threshold widening:
  Cousot and Cousot 1977; Blanchet et al., PLDI 2003.
- **Known bits.** Vishwanathan, Shachnai, Narayana and Nagarakatte, "Sound, precise, and fast
  abstract
  interpretation with tristate numbers", CGO 2022 (`tnum_add`, `tnum_sub`, `our_mul`); the same
  representation as LLVM's `KnownBits` and the Linux eBPF verifier's `tnum`.
- **Wrapping intervals.** Navas, Schachte, Søndergaard and Stuckey, "Signedness-agnostic program
  analysis: precise integer bounds for low-level code", APLAS 2012: arcs of the circle, the north
  and
  south poles, join by minimal cover, widening by doubling.
- **Congruences.** Granger, "Static analysis of arithmetical congruences", Int. J. Computer
  Mathematics, 1989, which also gives the interval and congruence reduction.
- **Reduced product.** Cousot and Cousot 1979; Cousot, Cousot and Mauborgne, "The reduced product of
  abstract domains and the combination of decision procedures", FoSSaCS 2011.
- **Sign-separated bits and bounds.** Fan et al., "Program Analysis Combining Generalized
  Bit-Level and Word-Level Abstractions", ISSTA 2025, DOI 10.1145/3728905. DOM-9 specifies a
  Galois adaptation and a stronger reduction; it does not claim full paper transfer parity.
- **Demanded bits.** LLVM's `DemandedBits` analysis, stated here as a relational agreement so that
  soundness is a theorem about two evaluations, with forward constants as premises.
- **Memory.** Site-and-offset addresses as in Miné, "Field-sensitive value analysis of embedded C
  programs with union types and pointer arithmetics", LCTES 2006; points-to sets as in Andersen's
  thesis (1994); byte-range sets as sorted interval lists.
- **Equality and numbering.** Alpern, Wegman and Zadeck, "Detecting equality of variables in
  programs", POPL 1988 (partitions; the join is the intersection); Cocke and Schwartz 1970 and
  Briggs, Cooper and Simpson, "Value numbering", 1997; hash-consing as in Filliâtre and Conchon,
  ML Workshop 2006.

## Performance notes

- Constants, signs, intervals and congruence arithmetic cost a constant number of `Z` operations per
  transfer. Known-bits transfers use O(1) big-integer operations except variable shifts, which use
  O(1 + log w), and variable rotations, which use O(w), on O(w)-bit integers for operand width `w`.
  This counts big-integer operations, not bit complexity; scalar shifts guard oversized amounts.
  Wrapped-interval multiplication is a constant number of cases. `tagged_domain` adds one width
  comparison per join.
- `capped` carriers hold their proof in `Prop`: they extract to the bare payload. Ranks sum over
  widths
  up to the cap and occur only in proofs. A reduced product calls `reduce` after each transfer, join
  and meet; `reduce_bits_wrapped` is a fixed two rounds.
- Byte-range operations are linear merges of sorted lists; the ranges per object stay few. A
  partition's `leb` is O(n) finds with compression; its join groups the keys of both supports in one
  pass through a `Map` keyed by the pair of representatives, O(n log n) in the support. `intern` is
  one `Table.get` and at most one `Table.set`.
- Prepared indexes: `numbering_wf` (a table with its next number) and `ranges_wf` (the canonical
  list), with agreement lemmas `intern_injective` and `ranges_ext`.
- DOM-9's feasible-extremum search visits at most `w` positions with O(w)-bit operands. A transfer
  uses at most eight input-branch combinations, plus component costs and reduction. The proposed
  join widening may require exponentially many improvements in `w`; these are cost estimates,
  not benchmark results or a whole-analysis complexity claim.

## Open questions

1. **Monotone transfers.** The laws give soundness and widening termination only. No theorem claims
   that `forward` is monotone, so Fixpoint's least-solution theorems do not apply to numeric
   systems.
2. **Precision.** The rule lists describe the intended transfers. The proved contract is soundness
   (`word_laws`, `numeric_laws`); a card may be more precise if the laws hold.
3. **Open cards.** DOM-6 now also holds footprints and the must lattice of ranges, and DOM-7 holds
   partition forgetting; if either outgrows its budget it splits along the file boundaries of the
   Files table.

## Notes for other documents

Renames and requests that follow from this document (document, old name or text, new name or text).

1. analyses.md: `range_must T` becomes `range_must ET`; raw lists enter the canonical carrier via
   `range_reached ET F`. `range_add fs a` becomes `range_add ET fs a` (in `validated_system` and
   `dead_store_transfer`); `range_must_top ET`, `range_must_lattice ET`, `range_remove ET fs a`
   and `range_covers a t o w` use the same encoding-indexed carrier.
2. analyses.md: `range_must_lattice` merges adjacent footprints and `range_covers` means bytewise
   coverage, including zero-width accesses. `validated_sound` needs `accessible` to follow from
   bytewise coverage, including the empty access, or needs a suitable premise and statement.
3. analyses.md request 3: `partition_forget_spec` holds under `p <> Unreached`; use
   `partition_forget_unreached` at `Unreached`. `partition` is `lift_bot {u | UnionFind.wf E u}`.
4. examples.md: `const_domain : numeric_domain const_fact` becomes `tagged_domain const_domain :
   numeric_domain (tagged (flat Z))` with `tagged_gamma const_gamma`; `nlat` and `nconc` are `lat`
   and `gamma` of that domain. examples.md also names a toy constructor `Fin`; the interval bound
   constructor of this document is `Fin` too, so one of them should be renamed.
5. Analyses and Examples use `Bits.expr` and `Bits.eval` from the Bits expression module.
6. TASKS.md, LEDGER.md and the cards: DOM-1 becomes DOM-1a (ORD-1, BIT-1) and DOM-1b (DOM-1a);
   VIEW-4 and ANA-8 list DOM-1a; DOM-2 and DOM-3 list DOM-1a; DOM-4 and DOM-6 also list DOM-1b;
   DOM-7 lists BIT-1 (`expr_key` uses `op_encoding` and `commutative`).

## Selectable signed bit-and-bounds domain (DOM-9)

### Representation and meaning

```coq
Inductive sb_half : Type :=
  | SBEmpty
  | SBRange (bits : tnum) (lo hi : Z).

Record signed_bounds : Type := SignedBounds {
  sb_zero : sb_half;
  sb_one : sb_half
}.

Definition sb_bit_gamma (w : width) (sign : bool) (h : sb_half) (z : Z) : Prop.
Definition sb_interval_gamma (w : width) (sign : bool) (h : sb_half) (z : Z) : Prop.
Definition sb_half_gamma (w : width) (sign : bool) (h : sb_half) (z : Z) : Prop.
Definition signed_bounds_gamma (w : width) (a : signed_bounds) (z : Z) : Prop.
Definition sb_reduce_half (w : width) (sign : bool) (h : sb_half) : sb_half.
Definition signed_bounds_reduce (w : width) (a : signed_bounds) : signed_bounds.
```

For either component gamma, require `is_word w z` and the most significant bit of z equal to
`sign`. `SBEmpty` means false in both. In `SBRange t lo hi`, bit gamma additionally means
`tnum_gamma w t z`; interval gamma additionally means `lo <= z <= hi`. Half gamma is their
conjunction, and signed-bounds gamma is the union of the half gammas, with false/true sign for
`sb_zero`/`sb_one`. Thus out-of-range raw bounds are intersected with the hemisphere, not wrapped;
tnum masks have exactly DOM-2's modulo-width meaning. The stored constructor has no width: its
meaning and all operations take the width explicitly.

For a half, let S be exactly the finite words satisfying half gamma. If S is empty, reduction
returns `SBEmpty`. Otherwise return `SBRange t l u` with l and u respectively the minimum and
maximum of S, and t the unique normalized mask identifying exactly the bits constant throughout
S (and leaving all other bits unknown). Thus its two components are their independently least
abstractions of S. Normalize masks to w bits and use a single canonical empty representation.
`signed_bounds_reduce` applies this separately to both halves.

Implement S's extrema by traversing word bits most-significant first with tight lower/upper
constraints and known bits. Choose a feasible 0 or 1 and retain enough state to backtrack or use
dynamic feasibility; return `None` exactly when no word exists. Do not enumerate words in the
implementation. Compute the tnum hull by intersecting the old masks with the interval bit hull
of the computed feasible extrema, and prove that equality against the set definition above.
An independently proved equivalent bit algorithm is permitted. This strengthening is not a
claim that the paper's artifact uses nearest-feasible endpoints.

```coq
Theorem sb_reduce_half_gamma : forall w s h z,
  sb_half_gamma w s (sb_reduce_half w s h) z <-> sb_half_gamma w s h z.
Theorem sb_reduce_half_idempotent : forall w s h,
  sb_reduce_half w s (sb_reduce_half w s h) = sb_reduce_half w s h.
Theorem sb_reduce_half_hulls : forall w s h q,
  (forall x, sb_half_gamma w s h x -> sb_bit_gamma w s q x) ->
  (forall z, sb_bit_gamma w s (sb_reduce_half w s h) z -> sb_bit_gamma w s q z).
Theorem sb_reduce_half_interval_hull : forall w s h q,
  (forall x, sb_half_gamma w s h x -> sb_interval_gamma w s q x) ->
  (forall z, sb_interval_gamma w s (sb_reduce_half w s h) z ->
    sb_interval_gamma w s q z).
Theorem signed_bounds_reduce_gamma : forall w a z,
  signed_bounds_gamma w (signed_bounds_reduce w a) z <-> signed_bounds_gamma w a z.
Theorem signed_bounds_reduce_idempotent : forall w a,
  signed_bounds_reduce w (signed_bounds_reduce w a) = signed_bounds_reduce w a.
```

The hull claims quantify over arbitrary raw `q` and only words in the indicated hemisphere.
They are stronger than soundness or stability of a particular sequence of exchanges. They do
not state that arbitrary operation transfer results are best abstractions of concrete results.
The raw-input conventions ensure the empty case is covered, including contradictory tnums.

### Lattice, operations and consumers

```coq
Definition signed_bounds_lattice (w : width) : lattice signed_bounds.
Definition signed_bounds_wrank (w : width) :
  bounded_widening_rank (signed_bounds_lattice w).
Definition signed_bounds_domain : word_domain signed_bounds.
Definition signed_bounds_classic_domain : word_domain signed_bounds.
Definition signed_bounds_numeric : numeric_domain (tagged signed_bounds) :=
  tagged_domain signed_bounds_domain.
Definition signed_bounds_capped (maxw : width) :
  numeric_domain (@capped signed_bounds maxw) := capped_domain signed_bounds_domain maxw.

Theorem signed_bounds_laws : forall w, lattice_laws (signed_bounds_lattice w).
Theorem signed_bounds_word_laws : word_laws signed_bounds_domain signed_bounds_gamma.
Theorem signed_bounds_classic_word_laws :
  word_laws signed_bounds_classic_domain signed_bounds_gamma.
Theorem signed_bounds_numeric_laws :
  numeric_laws signed_bounds_numeric (tagged_gamma signed_bounds_gamma).
Theorem signed_bounds_capped_laws : forall maxw,
  numeric_laws (signed_bounds_capped maxw) (capped_gamma signed_bounds_gamma maxw).
```

Every public lattice operation first reduces its raw input. The preorder compares the normalized
bit and interval components for inclusion separately per sign, with empty below all. Bottom has
both halves empty. Join takes the bit-mask join and interval hull per hemisphere, then reduces.
Widen is join; narrow returns its first input reduced. This finite-width widening is sound and
may take exponentially many strict interval-bound improvements in width; it deliberately omits
the paper's faster interval-doubling widening. Provide a decreasing bounded widening rank for
this exact definition, accounting for interval range growth and loss of fixed bits. Do not use
the bare weak lattice laws to infer leastness: prove any component hull or least join directly.
`pmeet` intersects both masks and intervals per sign and reduces. `ptop` has full hemispheres;
`pconst` creates the wrapped singleton in its sign hemisphere.

For forward transfer, split each input into at most two hemisphere branches, apply the landed
`known_bits_precise_domain` and `wrapped_domain` transfers to the corresponding masks and
non-wrapping interval arcs, split each result into its output sign hemispheres, join all
combinations, and reduce. The precise known-bit dictionary uses `tnum_mul_precise` for a
two-operand `bvmul` with both input widths equal to the result width, and otherwise delegates to
`known_bits_domain`. Its backward transfer is the existing DOM-2 transfer. The classic domain
uses `known_bits_domain` for forward transfer and otherwise has the same operations, reduction,
representation and meaning. `signed_bounds_domain`, `signed_bounds_numeric` and
`signed_bounds_capped` select the precise version; clients can use `tagged_domain` or
`capped_domain` with `signed_bounds_classic_domain` for the classic version. Both word-law
theorems hold for all raw inputs. Neither multiplier is required to dominate the other.

A circular output arc can intersect a hemisphere in two pieces; take the enclosing
interval hull of both pieces, rather than assuming their union is a single interval. There are
at most 2^3 combinations for valid Bits arity. The choice of widening and
the selected component transfers are a deliberate Galois adaptation; they do not promise the
paper's full tnum-plus operation precision. A result with a `WFull` arc splits to full intervals
in both output signs. For a malformed shape, use a sound fallback satisfying all `word_laws`.
For backward transfer, run each component `passume` on every input-branch combination and each
result branch, then intersect every returned branch with the corresponding original branch,
join all alternatives per operand and reduce. If the shape cannot be safely matched, return
the original operands reduced, preserving the exact list length. This guarantees
length/refinement even where evaluation is None.
The definitions must respect the existing component total zero-division, rotation, shift and
width-changing semantics. No non-emptiness assumption may be inferred from a merely consistent
mask without checking its interval intersection.

For numeric width `w`, DOM-8 multiplication returns bottom on contradictory masks; otherwise it
performs `w` stages, each with at most one scalar shift, tnum addition and join. The classic DOM-2
multiplication uses a constant number of big-integer operations, including its low-zero count.
Both return exact results for two constants, but DOM-8 still executes its width-bounded loop.
These are source-level operation counts, not bit complexity or benchmark results; operand sizes
and the cost of big-integer operations matter. Forward lifting invokes a component transfer for
at most eight branch combinations, with reduction and wrapped-transfer costs additional. Width is
positive, so there is no width-zero case. Malformed arities or widths retain the existing sound
fallback behavior; contradictory masks have empty concretisation.

### Pair-aware queries

Queries consume a whole reduced pair, not one constituent in isolation. They return `None` for
an empty selected sign. Otherwise unsigned bounds are the normalized inclusive endpoints, and
the known-bit answer is the normalized least mask for that half.

```coq
Definition signed_bounds_query (w : width) (a : signed_bounds) (s : bool) :
  option (tnum * Z * Z).
Theorem signed_bounds_query_sound : forall w a s t lo hi z,
  signed_bounds_query w a s = Some (t, lo, hi) ->
  sb_half_gamma w s (if s then sb_one a else sb_zero a) z ->
  tnum_gamma w t z /\ lo <= z <= hi.
Theorem signed_bounds_query_empty : forall w a s,
  signed_bounds_query w a s = None <->
  forall z, ~ sb_half_gamma w s (if s then sb_one a else sb_zero a) z.
Theorem signed_bounds_query_bounds_exact : forall w a s t lo hi,
  signed_bounds_query w a s = Some (t, lo, hi) ->
  sb_half_gamma w s (if s then sb_one a else sb_zero a) lo /\
  sb_half_gamma w s (if s then sb_one a else sb_zero a) hi.
```

For signed endpoints the consumer applies the existing `signed w` to these unsigned endpoints;
within each sign hemisphere the ordering is unchanged. Tagged clients pattern-match `TVal w a`,
and capped clients project the underlying tagged value; `TBot` has no values, while `TAny` has
no width-specific pair to query. No generic API record change is required.

<!-- AUD-API-NUM-BEGIN -->

# NUM source contracts

Definitions specify source work; future theorem types are proof obligations.

## Galois.Domains.DomainsAuditKnownBitsSource

Card: AUD-DOM-BASE

Source destination: `theories/Domains/DomainsAuditKnownBitsSource.v`.

```rocq
(** * Complete classic known-bit forward source equations

    This file expands every legacy forward branch, including variable shifts and raw list scans.
    For example, an empty first operand still evaluates every later strict emptiness test.
    Builds on: DomainPrimitive, BitsFun and DomainsKnownBits. *)

From Stdlib Require Import List NArith PArith ZArith Bool.
From Galois.Bits Require Import BitsWord BitsFun BitsOp.
From Galois.Domains Require Import DomainsKnownBits.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Domains Require Import DomainsAuditNumericCost.
Import List.ListNotations.

Definition kb_mark {A} (body : domain_run A) : domain_run A := domain_case 500 [] body.

Definition kb_unary (site : nat) (f : Z -> Z) (z : Z) : domain_run Z :=
  (f z, [AuditArithmetic site [count_zencode z]]).

Definition kb_half (w : width) : domain_run Z :=
  index <- domain_z DzSub (Z.pos w) 1 ;; domain_z DzPow 2 index.

Definition kb_signed (w : width) (z : Z) : domain_run Z := kb_mark (
  value <- domain_wrap w z ;;
  half_value <- kb_half w ;;
  positive <- domain_compare true value half_value ;;
  if positive then (value, []) else m <- domain_modulus w ;; domain_z DzSub value m).

Definition kb_msb (w : width) (z : Z) : domain_run bool :=
  value <- domain_wrap w z ;;
  index <- domain_z DzSub (Z.pos w) 1 ;; domain_testbit value index.

Definition kb_wctz (w : width) (z : Z) : domain_run Z := kb_mark (
  value <- domain_wrap w z ;;
  zero <- domain_equal value 0 ;;
  if zero then (Z.pos w, []) else
    first <- domain_wrap w z ;;
    second <- domain_wrap w z ;;
    negated <- domain_z DzSub 0 second ;;
    isolated <- domain_z DzAnd first negated ;; kb_unary 501 Z.log2 isolated).

Definition kb_wrotl (w : width) (z amount : Z) : domain_run Z :=
  wrapped_amount <- domain_wrap w amount ;;
  k <- domain_z DzMod wrapped_amount (Z.pos w) ;;
  first <- domain_wrap w z ;;
  power <- domain_z DzPow 2 k ;;
  shifted <- domain_z DzMul first power ;;
  second <- domain_wrap w z ;;
  complement <- domain_z DzSub (Z.pos w) k ;;
  divisor <- domain_z DzPow 2 complement ;;
  rest <- domain_z DzDiv second divisor ;;
  joined <- domain_z DzAdd shifted rest ;; domain_wrap w joined.

Definition kb_word_shift (o : op) (w : width) (z amount : Z) : domain_run Z := kb_mark (
  match o with
  | bvshl => domain_wshl w z amount
  | bvlshr =>
    first_amount <- domain_wrap w amount ;;
    oversized <- domain_compare false (Z.pos w) first_amount ;;
    if oversized then (0%Z, []) else
      value <- domain_wrap w z ;;
      second_amount <- domain_wrap w amount ;;
      power <- domain_z DzPow 2 second_amount ;; domain_z DzDiv value power
  | bvashr =>
    first_amount <- domain_wrap w amount ;;
    oversized <- domain_compare false (Z.pos w) first_amount ;;
    if oversized then
      negative <- kb_msb w z ;;
      if negative then m <- domain_modulus w ;; domain_z DzSub m 1 else (0%Z, [])
    else
      value <- kb_signed w z ;;
      second_amount <- domain_wrap w amount ;;
      power <- domain_z DzPow 2 second_amount ;;
      quotient <- domain_z DzDiv value power ;; domain_wrap w quotient
  | bvrotl => kb_wrotl w z amount
  | bvrotr =>
    wrapped <- domain_wrap w amount ;;
    reduced <- domain_z DzMod wrapped (Z.pos w) ;;
    complement <- domain_z DzSub (Z.pos w) reduced ;; kb_wrotl w z complement
  | _ => domain_wrap w z
  end).

Definition kb_scalar_value (o : op) (w : width) (amount z : Z) : domain_run Z := kb_mark (
  match o with
  | bvshl | bvlshr | bvashr =>
    reduced <- domain_z DzMin amount (Z.pos w) ;; kb_word_shift o w z reduced
  | bvrotl => reduced <- domain_z DzMod amount (Z.pos w) ;; kb_wrotl w z reduced
  | bvrotr =>
    negative <- domain_z DzSub 0 amount ;;
    reduced <- domain_z DzMod negative (Z.pos w) ;; kb_wrotl w z reduced
  | _ => domain_wrap w z
  end).

(** An internal map callback executes independently at both actual endpoints. *)
Definition kb_map (sw rw : width) (f : Z -> domain_run Z) (a : tnum) : domain_run tnum :=
  upper <- domain_max sw a ;;
  first <- f upper ;;
  z <- domain_wnot rw first ;;
  lower <- domain_min sw a ;;
  second <- f lower ;;
  o <- domain_wrap rw second ;; domain_tnum z o.

Definition kb_scalar o w amount a := kb_map w w (kb_scalar_value o w amount) a.

Definition kb_not (w : width) (a : tnum) : domain_run tnum := kb_mark (
  z <- domain_wrap w (ones a) ;;
  o <- domain_wrap w (zeros a) ;; domain_tnum z o).

Definition kb_bitop (o : op) (w : width) (a b : tnum) : domain_run tnum := kb_mark (
  match o with
  | bvand =>
    z <- domain_word_bits DzOr w (zeros a) (zeros b) ;;
    v <- domain_word_bits DzAnd w (ones a) (ones b) ;; domain_tnum z v
  | bvor =>
    z <- domain_word_bits DzAnd w (zeros a) (zeros b) ;;
    v <- domain_word_bits DzOr w (ones a) (ones b) ;; domain_tnum z v
  | _ =>
    zz <- domain_word_bits DzAnd w (zeros a) (zeros b) ;;
    oo <- domain_word_bits DzAnd w (ones a) (ones b) ;;
    z <- domain_word_bits DzOr w zz oo ;;
    zo <- domain_word_bits DzAnd w (zeros a) (ones b) ;;
    oz <- domain_word_bits DzAnd w (ones a) (zeros b) ;;
    v <- domain_word_bits DzOr w zo oz ;; domain_tnum z v
  end).

Definition kb_constant (w : width) (a : tnum) : domain_run (option Z) := kb_mark (
  first <- domain_wrap w (zeros a) ;;
  second <- domain_wnot w (ones a) ;;
  equal <- domain_equal first second ;;
  if equal then value <- domain_min w a ;; domain_return 502 [] (Some value)
  else domain_return 502 [] None).

Definition kb_sub (w : width) (a b : tnum) : domain_run tnum :=
  opposite <- kb_not w b ;; domain_adc w a opposite true.

Definition kb_trailing (w : width) (a : tnum) : domain_run Z :=
  possible <- domain_wnot w (zeros a) ;; kb_wctz w possible.

Definition kb_classic_mul (w : width) (a b : tnum) : domain_run tnum := kb_mark (
  first <- kb_constant w a ;;
  match first with
  | Some x => second <- kb_constant w b ;; match second with
    | Some y =>
    product <- domain_z DzMul x y ;;
    word <- domain_wrap w product ;; domain_const w word
    | None =>
    ta <- kb_trailing w a ;;
    tb <- kb_trailing w b ;;
    trailing <- domain_z DzAdd ta tb ;;
    mask <- kb_unary 503 Z.ones trailing ;;
    z <- domain_wrap w mask ;; domain_tnum z 0
    end
  | None =>
    ta <- kb_trailing w a ;;
    tb <- kb_trailing w b ;;
    trailing <- domain_z DzAdd ta tb ;;
    mask <- kb_unary 503 Z.ones trailing ;;
    z <- domain_wrap w mask ;; domain_tnum z 0
  end).

Definition kb_bitlen (h : Z) : domain_run Z := kb_mark (
  zero <- domain_equal h 0 ;;
  if zero then (0%Z, []) else
    logarithm <- kb_unary 501 Z.log2 h ;; domain_z DzAdd logarithm 1).

Definition kb_upper (w : width) (h : Z) : domain_run tnum :=
  bits <- kb_bitlen h ;;
  mask <- kb_unary 503 Z.ones bits ;;
  z <- domain_wnot w mask ;; domain_tnum z 0.

Definition kb_stride o (w : width) d : domain_run Z := kb_mark (
  doubled <- domain_z DzMul 2 d ;;
  if tnum_rotation o then domain_z DzMod doubled (Z.pos w) else (doubled, [])).

(** The actual binary mask chooses each recursion, shift, join and normalized stride. *)
Fixpoint kb_expand o w (fuel : positive) (distance : Z) (current : tnum) : domain_run tnum :=
  kb_mark (match fuel with
  | xH => shifted <- kb_scalar o w distance current ;; domain_tnum_bits DzAnd w current shifted
  | xO rest => next <- kb_stride o w distance ;; kb_expand o w rest next current
  | xI rest =>
    next <- kb_stride o w distance ;;
    shifted <- kb_scalar o w distance current ;;
    joined <- domain_tnum_bits DzAnd w current shifted ;; kb_expand o w rest next joined
  end).

Definition kb_expand_mask o w (mask : Z) current : domain_run tnum := kb_mark (
  match mask with
  | Zpos fuel => kb_expand o w fuel 1 current
  | _ => domain_normalise w current
  end).

Definition kb_variable_raw o w (a b : tnum) : domain_run tnum := kb_mark (
  base <- domain_min w b ;;
  mask <- domain_mask w b ;;
  current <- kb_scalar o w base a ;;
  if tnum_rotation o then kb_expand_mask o w mask current else
    before <- domain_z DzSub (Z.pos w) 1 ;;
    cutoff_bits <- kb_bitlen before ;;
    cutoff <- domain_z DzPow 2 cutoff_bits ;;
    low_mask <- domain_z DzMod mask cutoff ;;
    low <- kb_expand_mask o w low_mask current ;;
    small <- domain_compare true mask cutoff ;;
    if small then (low, []) else
      oversized <- kb_scalar o w (Z.pos w) a ;; domain_tnum_bits DzAnd w low oversized).

Definition kb_variable o w (a b : tnum) : domain_run tnum := kb_mark (
  first <- domain_empty w a ;;
  second <- domain_empty w b ;;
  if first || second then domain_bottom w else kb_variable_raw o w a b).

Definition kb_order (strict : bool) w (a b : tnum) : domain_run tnum := kb_mark (
  upper_a <- domain_max w a ;;
  lower_b <- domain_min w b ;;
  first <- domain_compare strict upper_a lower_b ;;
  if first then domain_const 1%positive 1 else
    upper_b <- domain_max w b ;;
    lower_a <- domain_min w a ;;
    second <- domain_compare (negb strict) upper_b lower_a ;;
    if second then domain_const 1%positive 0 else domain_tnum 0 0).

Definition kb_equal w (a b : tnum) : domain_run tnum := kb_mark (
  meet <- domain_tnum_bits DzOr w a b ;;
  empty <- domain_empty w meet ;;
  if empty then domain_const 1%positive 0 else
    first <- kb_constant w a ;;
    match first with
    | Some x => second <- kb_constant w b ;; match second with
      | Some y => equal <- domain_equal x y ;;
      domain_const 1%positive (if equal then 1 else 0)
      | None => domain_tnum 0 0
      end
    | None => domain_tnum 0 0
    end).

Definition kb_bias w a : domain_run tnum :=
  sign <- kb_half w ;;
  constant <- domain_const w sign ;; kb_bitop bvxor w a constant.

Definition kb_compare o w a b : domain_run tnum := kb_mark (
  match o with
  | bveq => kb_equal w a b
  | bvne => equal <- kb_equal w a b ;; kb_not 1%positive equal
  | bvult => kb_order true w a b
  | bvule => kb_order false w a b
  | bvslt | bvsle =>
    first <- kb_bias w a ;;
    second <- kb_bias w b ;;
    kb_order (match o with bvslt => true | _ => false end) w first second
  | _ => domain_tnum 0 0
  end).

Definition kb_concat (w v : width) (a b : tnum) : domain_run tnum := kb_mark (
  first <- domain_wrap w (zeros a) ;;
  m1 <- domain_modulus v ;;
  scaled1 <- domain_z DzMul first m1 ;;
  second <- domain_wrap v (zeros b) ;;
  sum1 <- domain_z DzAdd scaled1 second ;;
  let target1 := Pos.add w v in
  z <- domain_wrap target1 sum1 ;;
  third <- domain_wrap w (ones a) ;;
  m2 <- domain_modulus v ;;
  scaled2 <- domain_z DzMul third m2 ;;
  fourth <- domain_wrap v (ones b) ;;
  sum2 <- domain_z DzAdd scaled2 fourth ;;
  let target2 := Pos.add w v in
  value <- domain_wrap target2 sum2 ;;
  let '(out, body) := domain_tnum z value in
  (out, AuditArithmetic 504 [N.pos w; N.pos v] ::
    AuditArithmetic 504 [N.pos w; N.pos v] :: body)).

Definition kb_unary_map o sw rw a : domain_run tnum := kb_mark (
  match o with
  | bvzext _ | bvtrunc _ => kb_map sw rw (domain_wrap rw) a
  | bvsext _ => kb_map sw rw (fun z => value <- kb_signed sw z ;; domain_wrap rw value) a
  | bvextract _ lo => kb_map sw rw (fun z =>
    let amount := Z.of_nat lo in
    let prefix := [AuditArithmetic 505 [N.of_nat lo]] in
    let '(out, body) := power <- domain_z DzPow 2 amount ;;
      quotient <- domain_z DzDiv z power ;; domain_wrap rw quotient in
    (out, prefix ++ body)) a
  | _ => domain_tnum 0 0
  end).

(** Every legacy raw forward constructor retains its native malformed-list behavior. *)
Definition kb_forward_raw_source o (args : list (width * tnum)) rw : domain_run tnum := kb_mark (
  match o, args with
  | bvnot, [(_, a)] => kb_not rw a
  | bvneg, [(_, a)] => zero <- domain_const rw 0 ;; kb_sub rw zero a
  | (bvclz | bvctz | bvpopcnt), [_] => kb_upper rw (Z.pos rw)
  | bvadd, [(_, a); (_, b)] => domain_adc rw a b false
  | bvsub, [(_, a); (_, b)] => kb_sub rw a b
  | bvmul, [(_, a); (_, b)] => kb_classic_mul rw a b
  | bvudiv, [(_, a); (_, b)] =>
    divisor <- domain_wrap rw (ones b) ;;
    zero <- domain_equal divisor 0 ;;
    if zero then domain_tnum 0 0 else upper <- domain_max rw a ;; kb_upper rw upper
  | bvurem, [(_, a); _] => upper <- domain_max rw a ;; kb_upper rw upper
  | bvsrem, [(_, a); _] =>
    sign <- kb_half rw ;;
    clear <- domain_word_bits DzAnd rw (zeros a) sign ;; domain_tnum clear 0
  | (bvand | bvor | bvxor), [(_, a); (_, b)] => kb_bitop o rw a b
  | (bvshl | bvlshr | bvashr | bvrotl | bvrotr), [(_, a); (_, b)] => kb_variable o rw a b
  | (bveq | bvne | bvult | bvule | bvslt | bvsle), [(w, a); (_, b)] => kb_compare o w a b
  | bvite, [(_, condition); (_, a); (_, b)] =>
    constant <- kb_constant 1%positive condition ;;
    match constant with
    | None => domain_tnum_bits DzAnd rw a b
    | Some value => equal <- domain_equal value 1 ;;
      domain_normalise rw (if equal then a else b)
    end
  | (bvzext _ | bvtrunc _ | bvsext _ | bvextract _ _), [(w, a)] => kb_unary_map o w rw a
  | bvconcat, [(w, a); (v, b)] => kb_concat w v a b
  | _, _ => domain_tnum 0 0
  end).

(** Strict existsb evaluates the complete recursive tail even when the head is empty. *)
Fixpoint kb_any_empty_source (args : list (width * tnum)) : domain_run bool := kb_mark (
  match args with
  | [] => (false, [])
  | (w, a) :: rest =>
    first <- domain_empty w a ;;
    later <- kb_any_empty_source rest ;;
    (first || later, [AuditCase 506 [if first then 1%N else 0%N; if later then 1%N else 0%N]])
  end).

Definition kb_forward_source o args rw : domain_run tnum := kb_mark (
  empty <- kb_any_empty_source args ;;
  if empty then domain_bottom rw else kb_forward_raw_source o args rw).

Definition kb_frame_weight (event : audit_event unit) : nat :=
  match event with
  | AuditCase 500 _ => 100%nat
  | AuditArithmetic 501 [z] => S (audit_z_bits (count_zdecode z))
  | AuditArithmetic 503 [z] => audit_shift_weight 1 (count_zdecode z)
  | AuditArithmetic 504 [a; b] => audit_binary_weight (Z.of_N a) (Z.of_N b)
  | AuditArithmetic 505 [lo] => S (N.to_nat lo)
  | _ => domain_frame_weight event
  end.

Definition kb_source_work (events : audit_trace unit) : nat :=
  fold_right (fun event total => (kb_frame_weight event + total)%nat) 0%nat events.

(** Complete erasure covers every operator, raw sign/mask case and malformed operand list. *)
Definition kb_forward_source_erases_type : Prop := forall o args rw,
  fst (kb_forward_source o args rw) = tnum_forward o args rw.

(** The strict scan visits all input entries independently of where emptiness is first found. *)
Definition kb_empty_scan_source_count_type : Prop := forall args,
  (length args <= audit_case_count 500 (snd (kb_any_empty_source args)))%nat.
```

## Galois.Domains.DomainsAuditMul

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMul.v`.

```rocq
(** * Multiplier statement check

    This scratch file elaborates selected multiplier propositions.
    For example, their meet has the intersection of both component gammas.
    Builds on: DomainsKnownBitsFast and DomainsNumeric. *)

From Stdlib Require Import ZArith NArith PArith List Bool.
From Galois.Order Require Import OrderLattice.
From Galois.Bits Require Import BitsWord BitsFun BitsOp.
From Galois.Domains Require Import DomainsNumeric DomainsKnownBits DomainsKnownBitsFast.
From Galois.Domains Require Import DomainsAuditMulPlain.

(** * Counted multiplier result type *)

(** * Future operations and proposition types *)


Definition audit_mul_sound_type : Prop := forall w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (audit_mul w a b) (wmul w x y).

Definition audit_mul_meet_intersection_type : Prop := forall w a b z,
  tnum_gamma w (audit_mul_meet w a b) z <->
    tnum_gamma w (audit_mul w a b) z /\
    tnum_gamma w (tnum_mul_precise w a b) z.

Definition audit_mul_meet_sound_type : Prop := forall w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (audit_mul_meet w a b) (wmul w x y).

Definition audit_mul_constants_type : Prop := forall w x y,
  audit_mul w (pconst known_bits_domain w x) (pconst known_bits_domain w y) =
    pconst known_bits_domain w (wmul w x y).
Definition audit_mul_bottom_type : Prop := forall w a b,
  tnum_empty w a || tnum_empty w b = true ->
  audit_mul w a b = bot (tnum_lattice w).
Definition audit_mul_width_type : Prop := forall w a b,
  tnum_normalise w (audit_mul w a b) = audit_mul w a b.
Definition audit_mul_meet_constants_type : Prop := forall w x y,
  audit_mul_meet w (pconst known_bits_domain w x) (pconst known_bits_domain w y) =
    pconst known_bits_domain w (wmul w x y).
Definition audit_mul_meet_bottom_type : Prop := forall w a b,
  tnum_empty w a || tnum_empty w b = true ->
  audit_mul_meet w a b = bot (tnum_lattice w).
Definition audit_mul_meet_width_type : Prop := forall w a b,
  tnum_normalise w (audit_mul_meet w a b) = audit_mul_meet w a b.

Definition audit_mul_word_laws_type : Prop := word_laws audit_mul_domain tnum_gamma.
Definition audit_mul_meet_word_laws_type : Prop := word_laws audit_mul_meet_domain tnum_gamma.

Definition audit_mul_active_bits (w : width) (b : tnum) : N :=
  N.size (Z.to_N (wor w (tnum_min w b) (tnum_mask w b))).


Definition audit_mul_active_bits_bound_type : Prop := forall w b,
  (audit_mul_active_bits w b <= N.pos w)%N.
Definition audit_mul_counted_bounds_type : Prop := forall w a b,
  let '(_, work) := audit_mul_counted w a b in
  let active := audit_mul_active_bits w b in
  (audit_mul_steps work <= active /\ audit_mul_tests work <= 2 * active /\
   audit_mul_additions work <= N.succ active /\ audit_mul_shifts work <= active /\
   audit_mul_products work <= 1)%N.
Definition audit_mul_steps_exact_type : Prop := forall w a b,
  tnum_empty w a || tnum_empty w b = false ->
  audit_mul_steps (snd (audit_mul_counted w a b)) = audit_mul_active_bits w b.
```

## Galois.Domains.DomainsAuditMulDispatch

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMulDispatch.v`.

```rocq
(** * Complete multiplier dispatcher and legacy fallback
    Both width guards are strict. Classic fallback is the fixed shared KB body.
    Builds on: MulWhole and KnownBitsWhole. *)
From Stdlib Require Import List NArith PArith ZArith Bool.
From Galois.Bits Require Import BitsWord BitsOp.
From Galois.Domains Require Import DomainsNumeric DomainsKnownBits DomainsKnownBitsFast.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Domains Require Import DomainsAuditNumericCost.
From Galois.Domains Require Import DomainsAuditKnownBitsSource.
From Galois.Domains Require Import DomainsAuditNumericDimensions.
From Galois.Domains Require Import DomainsAuditMulSource.
Import ListNotations.
Definition domain_positive_eq a b : domain_run bool :=
 (Pos.eqb a b,[AuditArithmetic 550 [N.pos a;N.pos b]]).
Definition domain_positive_le a b : domain_run bool :=
 (Pos.leb a b,[AuditArithmetic 551 [N.pos a;N.pos b]]).
Definition mul_precise_forward_source o (args : list(width*tnum)) rw :=
 domain_case 552 [] (match o,args with bvmul,[(wa,a);(wb,b)] =>
 first <- domain_positive_eq wa rw ;; second <- domain_positive_eq wb rw ;;
 if first && second then mul_dom8_source rw a b else kb_forward_source o args rw
 | _,_ => kb_forward_source o args rw end).
Definition mul_dispatch_source (meet : bool) o (args : list(width*tnum)) rw :=
 domain_case 553 [] (match o,args with bvmul,[(wa,a);(wb,b)] =>
 first <- domain_positive_eq wa rw ;; second <- domain_positive_eq wb rw ;;
 if first && second then if meet then audit_mul_meet_source rw a b
 else out <- audit_mul_counted_source rw a b ;; domain_return 554 [] (fst out)
 else kb_forward_source o args rw | _,_ => kb_forward_source o args rw end).
Definition mul_dispatch_weight event := match event with
 | AuditArithmetic 550 [a;b] | AuditArithmetic 551 [a;b] => (2+N.size_nat a+N.size_nat b)%nat
 | AuditCase 552 _ | AuditCase 553 _ => 100%nat | _ => kb_frame_weight event end.
Definition mul_dispatch_work trace := fold_right (fun e n => (mul_dispatch_weight e+n)%nat) 0%nat
  trace.
Definition mul_precise_forward_erases_type : Prop := forall o args rw,
 fst(mul_precise_forward_source o args rw)=pforward known_bits_precise_domain o args rw.
Definition mul_dispatch_fallback_type : Prop := forall meet o args rw,
 (match o,args with bvmul,[(wa,_);(wb,_)] => Pos.eqb wa rw && Pos.eqb wb rw | _,_ => false
   end)=false ->
 fst(mul_dispatch_source meet o args rw)=tnum_forward o args rw.
Definition mul_dispatch_total_type : Prop := forall meet o args rw,
 exists result trace, mul_dispatch_source meet o args rw=(result,trace).
Definition mul_dispatch_unique_type : Prop := forall meet o args rw r1 t1 r2 t2,
 mul_dispatch_source meet o args rw=(r1,t1) -> mul_dispatch_source meet o args rw=(r2,t2) -> r1=r2
   /\ t1=t2.
Definition mul_dispatch_source_bound_type : Prop := forall meet o args rw,
 (mul_dispatch_work(snd(mul_dispatch_source meet o args rw)) <=
   numeric_envelope(numeric_kb_dimension o args rw))%nat.
```

## Galois.Domains.DomainsAuditMulPlain

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMulPlain.v`.

```rocq
(** * Concrete alternative multiplication

    The public bodies compute values and public statistics without an audit trace.
    For example, a known-zero multiplier performs no partial-product stage.
    Builds on: DomainsKnownBits and DomainsKnownBitsFast. *)

From Stdlib Require Import List NArith PArith ZArith Bool.
From Galois.Order Require Import OrderLattice.
From Galois.Bits Require Import BitsWord BitsFun BitsOp.
From Galois.Domains Require Import DomainsNumeric DomainsKnownBits DomainsKnownBitsFast.
Import List.ListNotations.

(** Public multiplication statistics are ordinary retained data. *)
Record audit_mul_work : Type := AuditMulWork {
  audit_mul_steps : N;
  audit_mul_tests : N;
  audit_mul_additions : N;
  audit_mul_shifts : N;
  audit_mul_products : N
}.

Definition audit_mul_update (tests : N) (active : bool) (work : audit_mul_work)
    : audit_mul_work :=
  AuditMulWork (N.succ (audit_mul_steps work))
    (if (tests =? 1)%N then N.succ (audit_mul_tests work)
     else (tests + audit_mul_tests work)%N)
    (if active then N.succ (audit_mul_additions work) else audit_mul_additions work)
    (if active then N.succ (audit_mul_shifts work) else audit_mul_shifts work)
    (audit_mul_products work).

Definition audit_mul_stage (w : width) (possible mask value multiplier_mask : Z)
    (state : Z * tnum * audit_mul_work) : Z * tnum * audit_mul_work :=
  let '(index, acc, work) := state in
  if Z.testbit value index then
    let shifted := wshl w mask index in
    let uncertainty := Tnum (wnot w shifted) 0 in
    ((index + 1)%Z, tnum_adc w acc uncertainty false, audit_mul_update 1 true work)
  else if Z.testbit multiplier_mask index then
    let shifted := wshl w possible index in
    let uncertainty := Tnum (wnot w shifted) 0 in
    ((index + 1)%Z, tnum_adc w acc uncertainty false, audit_mul_update 2 true work)
  else ((index + 1)%Z, acc, audit_mul_update 2 false work).

(** This fixed algorithm retains its public count record, but constructs no audit log. *)
Definition audit_mul_counted (w : width) (a b : tnum) : tnum * audit_mul_work :=
  if tnum_empty w a || tnum_empty w b then
    (bot (tnum_lattice w), AuditMulWork 0 0 0 0 0)
  else
    let va := tnum_min w a in
    let ma := tnum_mask w a in
    let vb := tnum_min w b in
    let mb := tnum_mask w b in
    let possible := wor w va ma in
    let multiplier := wor w vb mb in
    let active := N.size (Z.to_N multiplier) in
    let '(_, uncertainty, work) := N.iter active
      (audit_mul_stage w possible ma vb mb) (0%Z, tnum_const w 0, AuditMulWork 0 0 0 0 0) in
    let constant := tnum_const w (wrap w (va * vb)) in
    (tnum_adc w constant uncertainty false,
      AuditMulWork (audit_mul_steps work) (audit_mul_tests work)
        (N.succ (audit_mul_additions work)) (audit_mul_shifts work) 1).

(** The selected value path retains the actual public statistics computation. *)
Definition audit_mul (w : width) (a b : tnum) : tnum :=
  fst (audit_mul_counted w a b).

(** The meet intersects the alternative and the existing precise multiplier. *)
Definition audit_mul_meet (w : width) (a b : tnum) : tnum :=
  pmeet known_bits_domain w (audit_mul w a b) (tnum_mul_precise w a b).

Definition audit_mul_forward (meet : bool) (o : op) (args : list (width * tnum))
    (rw : width) : tnum :=
  match o, args with
  | bvmul, [(wa, a); (wb, b)] =>
    if Pos.eqb wa rw && Pos.eqb wb rw then
      if meet then audit_mul_meet rw a b else audit_mul rw a b
    else pforward known_bits_domain o args rw
  | _, _ => pforward known_bits_domain o args rw
  end.

Definition audit_mul_selected_domain (meet : bool) : word_domain tnum :=
  {| plat := plat known_bits_domain;
     ptop := ptop known_bits_domain;
     pconst := pconst known_bits_domain;
     pforward := audit_mul_forward meet;
     passume := passume known_bits_domain;
     pmeet := pmeet known_bits_domain |}.

Definition audit_mul_domain : word_domain tnum := audit_mul_selected_domain false.

Definition audit_mul_meet_domain : word_domain tnum := audit_mul_selected_domain true.
```

## Galois.Domains.DomainsAuditMulSource

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMulSource.v`.

```rocq
(** * Complete known-bit multiplication source equations

    This file composes the alternative, DOM-8 multiplier and final meet at their actual operands.
    For example, the meet branch executes both strict emptiness tests in both multipliers.
    Builds on: DomainPrimitive and DomainsKnownBitsFast. *)

From Stdlib Require Import List NArith PArith ZArith Bool.
From Galois.Order Require Import OrderLattice.
From Galois.Bits Require Import BitsWord BitsFun BitsOp.
From Galois.Domains Require Import DomainsNumeric DomainsKnownBits DomainsKnownBitsFast.
From Galois.Domains Require Import DomainsAuditMulPlain.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Domains Require Import DomainsAuditNumericCost.
Import List.ListNotations.

Record mul_stats : Type := MulStats {
  mul_steps : N;
  mul_tests : N;
  mul_adds : N;
  mul_shifts : N;
  mul_products : N
}.

Definition mul_zero : mul_stats := MulStats 0 0 0 0 0.

Definition mul_succ (n : N) : domain_run N :=
  (N.succ n, [AuditArithmetic 1 [n]]).

Definition mul_field (site : nat) (n : N) : domain_run N := (n, [AuditCase site [n]]).

(** Every statistic field is read and each selected successor and record is constructed. *)
Definition mul_update_stats (extra_tests : N) (active : bool) (stats : mul_stats)
    : domain_run mul_stats :=
  old_steps <- mul_field 260 (mul_steps stats) ;;
  steps <- mul_succ old_steps ;;
  old_tests <- mul_field 261 (mul_tests stats) ;;
  tests <- (if (extra_tests =? 1)%N then mul_succ old_tests else
    ((extra_tests + old_tests)%N, [AuditArithmetic 2 [extra_tests; old_tests]])) ;;
  old_adds <- mul_field 262 (mul_adds stats) ;;
  adds <- (if active then mul_succ old_adds else (old_adds, [])) ;;
  old_shifts <- mul_field 263 (mul_shifts stats) ;;
  shifts <- (if active then mul_succ old_shifts else (old_shifts, [])) ;;
  products <- mul_field 264 (mul_products stats) ;;
  domain_return 265 [steps; tests; adds; shifts; products]
    (MulStats steps tests adds shifts products).

Definition mul_uncertainty (w : width) (mask : Z) : domain_run tnum :=
  z <- domain_wnot w mask ;; domain_tnum z 0.

(** One alternative stage evaluates only its selected shift and addition. *)
Definition mul_stage (w : width) (possible mask value multiplier_mask : Z)
    (state : Z * tnum * mul_stats) : domain_run (Z * tnum * mul_stats) :=
  let '(index, acc, stats) := state in
  first <- domain_testbit value index ;;
  domain_case 266 [if first then 1%N else 0%N]
    (if first then
      next <- domain_z DzAdd index 1 ;;
      shifted <- domain_wshl w mask index ;;
      uncertainty <- mul_uncertainty w shifted ;;
      sum <- domain_adc w acc uncertainty false ;;
      updated <- mul_update_stats 1%N true stats ;;
      domain_return 267 [] (next, sum, updated)
    else
      second <- domain_testbit multiplier_mask index ;;
      domain_case 268 [if second then 1%N else 0%N]
        (if second then
          next <- domain_z DzAdd index 1 ;;
          shifted <- domain_wshl w possible index ;;
          uncertainty <- mul_uncertainty w shifted ;;
          sum <- domain_adc w acc uncertainty false ;;
          updated <- mul_update_stats 2%N true stats ;;
          domain_return 267 [] (next, sum, updated)
        else
          next <- domain_z DzAdd index 1 ;;
          updated <- mul_update_stats 2%N false stats ;;
          domain_return 267 [] (next, acc, updated))).

(** Top-level normalization, both emptiness tests, binary fuel and output are all composed. *)
Definition audit_mul_counted_source (w : width) (a b : tnum)
    : domain_run (tnum * mul_stats) :=
  empty_a <- domain_empty w a ;;
  empty_b <- domain_empty w b ;;
  let empty := empty_a || empty_b in
  domain_case 269 [if empty_a then 1%N else 0%N; if empty_b then 1%N else 0%N]
    (domain_case 270 [if empty then 1%N else 0%N]
      (if empty then
        bottom <- domain_bottom w ;;
        domain_return 271 [0%N; 0%N; 0%N; 0%N; 0%N] (bottom, mul_zero)
      else
        va <- domain_min w a ;;
        ma <- domain_mask w a ;;
        vb <- domain_min w b ;;
        mb <- domain_mask w b ;;
        possible <- domain_word_bits DzOr w va ma ;;
        multiplier <- domain_word_bits DzOr w vb mb ;;
        let as_N := Z.to_N multiplier in
        let active := N.size as_N in
        ignored <- domain_tell [AuditArithmetic 46 [count_zencode multiplier];
          AuditArithmetic 7 [as_N]] ;;
        initial <- domain_const w 0 ;;
        ignored <- domain_tell [AuditConstruct 267 [];
          AuditConstruct 265 [0%N; 0%N; 0%N; 0%N; 0%N]] ;;
        state <- domain_iter active (mul_stage w possible ma vb mb) (0%Z, initial, mul_zero) ;;
        let '(_, uncertainty, stats) := state in
        ignored <- domain_tell [AuditCase 272 []] ;;
        product <- domain_z DzMul va vb ;;
        wrapped <- domain_wrap w product ;;
        constant <- domain_const w wrapped ;;
        result <- domain_adc w constant uncertainty false ;;
        adds <- mul_succ (mul_adds stats) ;;
        ( (result, MulStats (mul_steps stats) (mul_tests stats) adds (mul_shifts stats) 1%N),
          [AuditCase 260 [mul_steps stats]; AuditCase 261 [mul_tests stats];
           AuditCase 262 [mul_adds stats]; AuditCase 263 [mul_shifts stats];
           AuditConstruct 265 [mul_steps stats; mul_tests stats; adds; mul_shifts stats; 1%N];
           AuditConstruct 273 []]))).

(** The precise multiplier's stage includes its strict output successor and selected operands. *)
Definition mul_dom8_stage (w : width) (a b : tnum) (state : Z * tnum)
    : domain_run (Z * tnum) :=
  domain_case 275 [] (
  let '(index, acc) := state in
  next <- domain_z DzAdd index 1 ;;
  z <- domain_zeros b ;;
  clear <- domain_testbit z index ;;
  out <- domain_case 276 [if clear then 1%N else 0%N] (if clear then (acc, []) else
    shifted <- domain_shift w index a ;;
    sum <- domain_adc w acc shifted false ;;
    o <- domain_ones b ;;
    set <- domain_testbit o index ;;
    domain_case 274 [if set then 1%N else 0%N]
      (if set then (sum, []) else domain_tnum_bits DzAnd w acc sum)) ;;
  domain_return 277 [] (next, out)).

Definition mul_dom8_source (w : width) (a b : tnum) : domain_run tnum :=
  empty_a <- domain_empty w a ;;
  empty_b <- domain_empty w b ;;
  let empty := empty_a || empty_b in
  domain_case 278 [if empty_a then 1%N else 0%N; if empty_b then 1%N else 0%N]
    (domain_case 279 [if empty then 1%N else 0%N]
      (if empty then domain_bottom w else
        initial <- domain_const w 0 ;;
        ignored <- domain_tell [AuditConstruct 277 []] ;;
        out <- domain_iter (N.pos w) (mul_dom8_stage w a b) (0%Z, initial) ;;
        (snd out, [AuditCase 280 []]))).

(** The meet runs both whole multipliers before executing the concrete known-bit meet. *)
Definition audit_mul_meet_source (w : width) (a b : tnum) : domain_run tnum :=
  let '((first, _), first_trace) := audit_mul_counted_source w a b in
  let '(second, second_trace) := mul_dom8_source w a b in
  let '(out, meet_trace) := domain_tnum_bits DzOr w first second in
  (out, first_trace ++ [AuditCase 280 []] ++ second_trace ++ meet_trace).

Definition mul_input_size w (a b : tnum) : nat :=
  (1 + Pos.to_nat w + audit_z_bits (zeros a) + audit_z_bits (ones a) +
    audit_z_bits (zeros b) + audit_z_bits (ones b))%nat.

(** The precise branch erases to the existing DOM-8 implementation on arbitrary raw masks. *)
Definition mul_dom8_source_erases_type : Prop := forall w a b,
  fst (mul_dom8_source w a b) = tnum_mul_precise w a b.

(** The selected branch counts every processed possible multiplier bit exactly. *)
Definition audit_mul_source_counts_type : Prop := forall w a b,
  let '((_, stats), _) := audit_mul_counted_source w a b in
  let active := N.size (Z.to_N (wor w (tnum_min w b) (tnum_mask w b))) in
  (mul_steps stats <= active /\ mul_tests stats <= 2 * active /\
    mul_adds stats <= active + 1 /\ mul_shifts stats <= active /\ mul_products stats <= 1)%N.

(** Whole alternative, precise and meet costs include all setup, repeated output and nested work. *)
Definition audit_mul_source_bound_type : Prop := forall w a b,
  let size := mul_input_size w a b in
  let budget := (10000000 * (Pos.to_nat w + 1) * (size + 1) * (size + 1))%nat in
  (domain_work (snd (audit_mul_counted_source w a b)) <= budget /\
    domain_work (snd (mul_dom8_source w a b)) <= budget /\
    domain_work (snd (audit_mul_meet_source w a b)) <= 3 * budget)%nat.

(** The fixed mirror preserves all public multiplication statistics as well as the value. *)
Definition audit_mul_counted_plain_erases_type : Prop := forall w a b,
  let '((result, work), _) := audit_mul_counted_source w a b in
  audit_mul_counted w a b =
    (result, AuditMulWork (mul_steps work) (mul_tests work) (mul_adds work)
      (mul_shifts work) (mul_products work)).

(** The meet mirror preserves the concrete public operation. *)
Definition audit_mul_meet_plain_erases_type : Prop := forall w a b,
  fst (audit_mul_meet_source w a b) = audit_mul_meet w a b.
```

## Galois.Domains.DomainsAuditNumericCost

Card: AUD-DOM-BASE

Source destination: `theories/Domains/DomainsAuditNumericCost.v`.

```rocq
(** * Fixed numeric helper bodies

    This file spells out the integer, word and known-bit helpers used by domain models.
    For example, a known-bit emptiness test executes both wrapped masks before comparing.
    Builds on: SignedOperand, the fixed vocabulary and DomainsKnownBits. *)

From Stdlib Require Import List NArith PArith ZArith Bool.
From Galois.Order Require Import OrderLattice.
From Galois.Bits Require Import BitsWord BitsFun BitsOp.
From Galois.Domains Require Import DomainsKnownBits.
From Galois.Collections Require Import CollectionsAuditCost.
Import List.ListNotations.

Definition domain_run (A : Type) : Type := A * audit_trace unit.

Definition domain_bind {A B} (first : domain_run A) (next : A -> domain_run B)
    : domain_run B :=
  let '(a, first_trace) := first in
  let '(b, next_trace) := next a in (b, first_trace ++ next_trace).

Notation "x <- first ;; next" := (domain_bind first (fun x => next))
  (at level 100, first at next level, right associativity).

Definition domain_return {A} (site : nat) (payload : list N) (value : A) : domain_run A :=
  (value, [AuditConstruct site payload]).

Definition domain_tell (events : audit_trace unit) : domain_run unit := (tt, events).

Definition domain_case {A} (site : nat) (payload : list N) (body : domain_run A)
    : domain_run A := (fst body, AuditCase site payload :: snd body).

(** Integer primitive identifiers fix their operation, with actual signed operands. *)
Inductive domain_zop : Type :=
  | DzAdd
  | DzSub
  | DzMul
  | DzDiv
  | DzMod
  | DzAnd
  | DzOr
  | DzXor
  | DzMin
  | DzMax
  | DzPow.

Definition domain_zop_site (op : domain_zop) : nat :=
  match op with
  | DzAdd => 200 | DzSub => 201 | DzMul => 202 | DzDiv => 203 | DzMod => 204
  | DzAnd => 205 | DzOr => 206 | DzXor => 207 | DzMin => 208 | DzMax => 209
  | DzPow => 210
  end%nat.

Definition domain_z (op : domain_zop) (a b : Z) : domain_run Z :=
  let out := match op with
    | DzAdd => (a + b)%Z | DzSub => (a - b)%Z | DzMul => (a * b)%Z
    | DzDiv => (a / b)%Z | DzMod => (a mod b)%Z | DzAnd => Z.land a b
    | DzOr => Z.lor a b | DzXor => Z.lxor a b | DzMin => Z.min a b
    | DzMax => Z.max a b | DzPow => (a ^ b)%Z
    end in
  (out, [scalar_z (domain_zop_site op) a b]).

Definition domain_not (a : Z) : domain_run Z :=
  (Z.lnot a, [AuditArithmetic 211 [count_zencode a]]).

Definition domain_compare (strict : bool) (a b : Z) : domain_run bool :=
  (if strict then (a <? b)%Z else (a <=? b)%Z,
    [scalar_z (if strict then 212 else 213)%nat a b]).

Definition domain_equal (a b : Z) : domain_run bool :=
  ((a =? b)%Z, [scalar_z 214 a b]).

Definition domain_testbit (a index : Z) : domain_run bool :=
  (Z.testbit a index, [scalar_z 215 a index]).

Definition domain_b2z (b : bool) : domain_run Z :=
  (Z.b2z b, [AuditCase 223 [if b then 1%N else 0%N]]).

Definition domain_modulus (w : width) : domain_run Z := domain_z DzPow 2 (Z.pos w).

Definition domain_wrap (w : width) (a : Z) : domain_run Z :=
  m <- domain_modulus w ;; domain_z DzMod a m.

Definition domain_wnot (w : width) (a : Z) : domain_run Z :=
  m <- domain_modulus w ;;
  upper <- domain_z DzSub m 1 ;;
  value <- domain_wrap w a ;; domain_z DzSub upper value.

Definition domain_word_bits (op : domain_zop) (w : width) (a b : Z) : domain_run Z :=
  lhs <- domain_wrap w a ;;
  rhs <- domain_wrap w b ;; domain_z op lhs rhs.

Definition domain_zeros (a : tnum) : domain_run Z :=
  (zeros a, [AuditCase 216 [count_zencode (zeros a)]]).

Definition domain_ones (a : tnum) : domain_run Z :=
  (ones a, [AuditCase 217 [count_zencode (ones a)]]).

Definition domain_tnum (z o : Z) : domain_run tnum :=
  domain_return 218 [count_zencode z; count_zencode o] (Tnum z o).

Definition domain_const (w : width) (a : Z) : domain_run tnum :=
  z <- domain_wnot w a ;;
  o <- domain_wrap w a ;; domain_tnum z o.

Definition domain_normalise (w : width) (a : tnum) : domain_run tnum :=
  za <- domain_zeros a ;;
  z <- domain_wrap w za ;;
  oa <- domain_ones a ;;
  o <- domain_wrap w oa ;; domain_tnum z o.

Definition domain_tnum_bits (op : domain_zop) (w : width) (a b : tnum)
    : domain_run tnum :=
  za <- domain_zeros a ;;
  zb <- domain_zeros b ;;
  z <- domain_word_bits op w za zb ;;
  oa <- domain_ones a ;;
  ob <- domain_ones b ;;
  o <- domain_word_bits op w oa ob ;; domain_tnum z o.

Definition domain_min (w : width) (a : tnum) : domain_run Z :=
  o <- domain_ones a ;; domain_wrap w o.

Definition domain_max (w : width) (a : tnum) : domain_run Z :=
  z <- domain_zeros a ;; domain_wnot w z.

Definition domain_mask (w : width) (a : tnum) : domain_run Z :=
  z <- domain_zeros a ;;
  o <- domain_ones a ;;
  combined <- domain_word_bits DzOr w z o ;; domain_wnot w combined.

Definition domain_empty (w : width) (a : tnum) : domain_run bool :=
  z <- domain_zeros a ;;
  o <- domain_ones a ;;
  overlap <- domain_word_bits DzAnd w z o ;;
  zero <- domain_equal overlap 0 ;;
  (negb zero, [AuditCase 219 [if zero then 1%N else 0%N]]).

Definition domain_bottom (w : width) : domain_run tnum :=
  m1 <- domain_modulus w ;;
  z <- domain_z DzSub m1 1 ;;
  m2 <- domain_modulus w ;;
  o <- domain_z DzSub m2 1 ;; domain_tnum z o.

Definition domain_subset (w : width) (a b : Z) : domain_run bool :=
  lhs <- domain_word_bits DzAnd w a b ;;
  rhs <- domain_wrap w a ;; domain_equal lhs rhs.

Definition domain_order (w : width) (a b : tnum) : domain_run bool :=
  zb <- domain_zeros b ;;
  za <- domain_zeros a ;;
  z <- domain_subset w zb za ;;
  ob <- domain_ones b ;;
  oa <- domain_ones a ;;
  o <- domain_subset w ob oa ;;
  (z && o, [AuditCase 220 [if z then 1%N else 0%N; if o then 1%N else 0%N]]).

(** Both carry streams and both unknown masks are evaluated in their literal source order. *)
Definition domain_uncertain (w : width) (a b : tnum) (initial : bool) : domain_run Z :=
  amin <- domain_min w a ;;
  bmin <- domain_min w b ;;
  sum_min <- domain_z DzAdd amin bmin ;;
  low_carry <- domain_b2z initial ;;
  low <- domain_z DzAdd sum_min low_carry ;;
  amax <- domain_max w a ;;
  bmax <- domain_max w b ;;
  sum_max <- domain_z DzAdd amax bmax ;;
  high_carry <- domain_b2z initial ;;
  high <- domain_z DzAdd sum_max high_carry ;;
  different <- domain_z DzXor low high ;;
  ma <- domain_mask w a ;;
  mb <- domain_mask w b ;;
  masks <- domain_z DzOr ma mb ;; domain_z DzOr different masks.

Definition domain_adc (w : width) (a b : tnum) (initial : bool) : domain_run tnum :=
  amin <- domain_min w a ;;
  bmin <- domain_min w b ;;
  sum <- domain_z DzAdd amin bmin ;;
  carry <- domain_b2z initial ;;
  value <- domain_z DzAdd sum carry ;;
  mask <- domain_uncertain w a b initial ;;
  either <- domain_z DzOr value mask ;;
  neg <- domain_not either ;;
  z <- domain_wrap w neg ;;
  nm <- domain_not mask ;;
  both <- domain_z DzAnd value nm ;;
  o <- domain_wrap w both ;; domain_tnum z o.

(** A word shift follows the actual cutoff, power, product and wrapping branches. *)
Definition domain_wshl (w : width) (a amount : Z) : domain_run Z :=
  first_amount <- domain_wrap w amount ;;
  oversized <- domain_compare false (Z.pos w) first_amount ;;
  domain_case 221 [if oversized then 1%N else 0%N]
    (if oversized then domain_return 222 [] 0%Z else
      x <- domain_wrap w a ;;
      second_amount <- domain_wrap w amount ;;
      power <- domain_z DzPow 2 second_amount ;;
      product <- domain_z DzMul x power ;; domain_wrap w product).

(** Mapping two endpoints retains the duplicated source evaluation of the shift function. *)
Definition domain_shift (w : width) (amount : Z) (a : tnum) : domain_run tnum :=
  first_max <- domain_max w a ;;
  first_amount <- domain_z DzMin amount (Z.pos w) ;;
  first <- domain_wshl w first_max first_amount ;;
  z <- domain_wnot w first ;;
  second_min <- domain_min w a ;;
  second_amount <- domain_z DzMin amount (Z.pos w) ;;
  second <- domain_wshl w second_min second_amount ;;
  o <- domain_wrap w second ;; domain_tnum z o.

(** Shared natural arithmetic sites have explicit prices, without importing scalar algorithms. *)
Definition domain_auxiliary_frame_weight (event : audit_event unit) : nat :=
  match event with
  | AuditArithmetic site [a] =>
    if Nat.eqb site 0 || Nat.eqb site 1 then audit_binary_weight (Z.of_N a) 0%Z
    else if Nat.eqb site 7 || Nat.eqb site 64 then
      audit_unary_conversion_weight (audit_z_bits (Z.of_N a))
    else if Nat.eqb site 46 then audit_unary_conversion_weight (audit_z_bits(count_zdecode a))
    else if Nat.eqb site 41 || Nat.eqb site 43 then S(N.to_nat a) else 1%nat
  | AuditArithmetic site [a;b] =>
    if Nat.eqb site 3 then audit_multiply_weight (Z.of_N a)(Z.of_N b)
    else if Nat.eqb site 4 || Nat.eqb site 5 then audit_divide_weight (Z.of_N a)(Z.of_N b)
    else if Nat.eqb site 42 || Nat.eqb site 82 then audit_divide_weight(count_zdecode
      a)(count_zdecode b)
    else if Nat.eqb site 44 || Nat.eqb site 60 || Nat.eqb site 63 then
      audit_binary_weight(count_zdecode a)(count_zdecode b)
    else if Nat.eqb site 65 then audit_multiply_weight(count_zdecode a)(count_zdecode b)
    else if Nat.eqb site 45 then (S(N.to_nat a)+audit_divide_weight(count_zdecode b)(2^Z.of_N
      a))%nat
    else audit_binary_weight (Z.of_N a)(Z.of_N b)
  | _ => 1%nat end.

(** Primitive costs are fixed, positive, and retain numeric shift or exponent sizes. *)
Definition domain_frame_weight (event : audit_event unit) : nat :=
  match event with
  | AuditArithmetic site [a; b] =>
    if Nat.eqb site 202 then audit_multiply_weight (count_zdecode a) (count_zdecode b)
    else if Nat.eqb site 203 || Nat.eqb site 204 then
      audit_divide_weight (count_zdecode a) (count_zdecode b)
    else if Nat.eqb site 210 then
      (1 + audit_z_bits (count_zdecode a) *
        S (Z.to_nat (Z.max 0 (count_zdecode b))))%nat
    else if (200 <=? site)%nat && (site <=? 215)%nat then
      audit_binary_weight (count_zdecode a) (count_zdecode b)
    else domain_auxiliary_frame_weight event
  | AuditArithmetic 211 [a] => S (audit_z_bits (count_zdecode a))
  | _ => domain_auxiliary_frame_weight event
  end.

Definition domain_work (events : audit_trace unit) : nat :=
  fold_right (fun event total => (domain_frame_weight event + total)%nat) 0%nat events.

(** Binary iteration executes both halves and retains every terminal source test. *)
Fixpoint domain_piter {A} (fuel : positive) (body : A -> domain_run A) (state : A)
    : domain_run A :=
  domain_case 224 [N.pos fuel]
    (match fuel with
    | xH => body state
    | xO p => mid <- domain_piter p body state ;; domain_piter p body mid
    | xI p => mid1 <- domain_piter p body state ;;
      mid2 <- domain_piter p body mid1 ;; body mid2
    end).

Definition domain_iter {A} (fuel : N) (body : A -> domain_run A) (state : A)
    : domain_run A :=
  domain_case 225 [fuel]
    (match fuel with
    | N0 => (state, [])
    | Npos p => domain_piter p body state
    end).

(** Helper erasure fixes concrete result identities before any whole-operation bound. *)
Definition domain_helpers_erases_type : Prop :=
  (forall w a, fst (domain_empty w a) = tnum_empty w a) /\
  (forall w a b initial, fst (domain_adc w a b initial) = tnum_adc w a b initial) /\
  (forall w amount a, fst (domain_shift w amount a) = tnum_scalar bvshl w amount a) /\
  (forall w a b, fst (domain_order w a b) = leb (tnum_lattice w) a b).

(** Every shared public helper names its exact existing result, independently of any cost bound. *)
Definition domain_helpers_full_erases_type : Prop :=
 (forall w, fst(domain_modulus w)=modulus w) /\
 (forall w z, fst(domain_wrap w z)=wrap w z) /\
 (forall w z, fst(domain_wnot w z)=wnot w z) /\
 (forall w z, fst(domain_const w z)=tnum_const w z) /\
 (forall w a, fst(domain_normalise w a)=tnum_normalise w a) /\
 (forall w a, fst(domain_min w a)=tnum_min w a) /\
 (forall w a, fst(domain_max w a)=tnum_max w a) /\
 (forall w a, fst(domain_mask w a)=tnum_mask w a) /\
 (forall w, fst(domain_bottom w)=bot(tnum_lattice w)) /\
 (forall w a b, fst(domain_tnum_bits DzAnd w a b)=tnum_join w a b) /\
 (forall w a b, fst(domain_tnum_bits DzOr w a b)=tnum_meet w a b) /\
 domain_helpers_erases_type.
```

## Galois.Domains.DomainsAuditNumericDimensions

Card: AUD-DOM-BASE

Source destination: `theories/Domains/DomainsAuditNumericDimensions.v`.

```rocq
(** * Input dimensions and nontrivial whole-source envelopes
    Numeric widths and unary extract indices are input dimensions, not logarithmic surrogates.
    Builds on: KnownBitsWhole and BitsOp. *)
From Stdlib Require Import List NArith PArith ZArith.
From Galois.Bits Require Import BitsWord BitsOp.
From Galois.Domains Require Import DomainsKnownBits.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Domains Require Import DomainsAuditNumericCost.
From Galois.Domains Require Import DomainsAuditKnownBitsSource.
Import ListNotations.
Definition numeric_operator_dimension o : nat := match o with
 | bvzext w | bvsext w | bvtrunc w => S(Pos.to_nat w)
 | bvextract hi lo => (1+hi+lo)%nat | _ => 1%nat end.
Definition numeric_tnum_dimension (a : tnum) := (1+audit_z_bits(zeros a)+audit_z_bits(ones a))%nat.
Definition numeric_kb_dimension o (args : list(width*tnum)) rw :=
 (1+numeric_operator_dimension o+Pos.to_nat rw+
 fold_right (fun wa n => (1+Pos.to_nat(fst wa)+numeric_tnum_dimension(snd wa)+n)%nat) 0%nat
   args)%nat.
Definition numeric_envelope (dimension : nat) := (10000000000 * Nat.pow (S dimension) 12)%nat.
Definition kb_forward_source_bound_type : Prop := forall o args rw,
 (kb_source_work(snd(kb_forward_source o args rw)) <= numeric_envelope(numeric_kb_dimension o args
   rw))%nat.
Definition kb_classic_mul_source_bound_type : Prop := forall w a b,
 (kb_source_work(snd(kb_classic_mul w a b)) <= numeric_envelope(numeric_kb_dimension bvmul
   [(w,a);(w,b)] w))%nat.
Definition kb_source_total_type : Prop := forall o args rw, exists r t, kb_forward_source o args
  rw=(r,t).
Definition kb_source_unique_type : Prop := forall o args rw r1 t1 r2 t2,
 kb_forward_source o args rw=(r1,t1) -> kb_forward_source o args rw=(r2,t2) -> r1=r2 /\ t1=t2.
```

## Galois.Domains.DomainsAuditProductSource

Card: AUD-DR-PRODUCT

Source destination: `theories/Domains/DomainsAuditProductSource.v`.

```rocq
(** * Concrete bits and wrapped exchange source equations

    This file expands the selected exchange through endpoint selection and repeated bit packing.
    For example, a successful pack bit recomputes the full depth for its setbit operand.
    Builds on: DomainPrimitive, DomainsProduct and DomainsWrapped. *)

From Stdlib Require Import List NArith PArith ZArith Bool.
From Galois.Bits Require Import BitsWord.
From Galois.Domains Require Import DomainsKnownBits DomainsWrapped DomainsProduct.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Domains Require Import DomainsAuditNumericCost.
Import List.ListNotations.

Definition product_offset_source (w : width) (origin value : Z) : domain_run Z :=
  delta <- domain_z DzSub value origin ;;
  m <- domain_modulus w ;; domain_z DzMod delta m.

Definition product_wrapped_norm_source (w : width) (a : wrapped) : domain_run wrapped :=
  domain_case 320 []
    (match a with
    | WItv lo hi =>
      offset <- product_offset_source w lo hi ;;
      m <- domain_modulus w ;;
      upper <- domain_z DzSub m 1 ;;
      full <- domain_equal offset upper ;;
      domain_case 321 [if full then 1%N else 0%N]
        (if full then domain_return 322 [] WFull else
          first <- domain_wrap w lo ;;
          last <- domain_wrap w hi ;;
          domain_return 323 [count_zencode first; count_zencode last] (WItv first last))
    | _ => (a, [])
    end).

Definition product_wrapped_order_source (w : width) (a b : wrapped) : domain_run bool :=
  domain_case 324 []
    (match a, b with
    | WBot, _ => (true, [])
    | _, WFull => (true, [])
    | _, WBot => (false, [])
    | WFull, WItv lo hi =>
      offset <- product_offset_source w lo hi ;;
      m <- domain_modulus w ;;
      upper <- domain_z DzSub m 1 ;; domain_equal offset upper
    | WItv a b, WItv c d =>
      span <- product_offset_source w c d ;;
      m <- domain_modulus w ;;
      upper <- domain_z DzSub m 1 ;;
      full <- domain_equal span upper ;;
      start <- product_offset_source w c a ;;
      inner <- product_offset_source w a b ;;
      ending <- domain_z DzAdd start inner ;;
      span_again <- product_offset_source w c d ;;
      included <- domain_compare false ending span_again ;;
      (full || included, [AuditCase 325 []])
    end).

Fixpoint product_depth_source (p : positive) : domain_run Z :=
  domain_case 326 [N.pos p]
    (match p with
    | xH => (0%Z, [])
    | xO q | xI q => depth <- product_depth_source q ;; domain_z DzAdd 1 depth
    end).

Definition product_tree_source (w : width) : domain_run positive :=
  domain_iter (N.pos w) (fun p => domain_return 327 [N.pos p] (xO p)) xH.

Definition product_odd_source (z : Z) : domain_run bool :=
  (Z.odd z, [AuditArithmetic 328 [count_zencode z]]).

Definition product_free_source (lo upper : Z) : domain_run Z :=
  half <- domain_z DzDiv lo 2 ;;
  equal <- domain_equal upper half ;;
  domain_case 329 [if equal then 1%N else 0%N]
    (if equal then domain_z DzMod lo 2 else (0%Z, [])).

(** Ceiling selects one child per binary digit and retains every quotient operand. *)
Fixpoint product_ceiling_source (p : positive) (zero one lo : Z)
    : domain_run (option Z) :=
  domain_case 330 [N.pos p]
    (match p with
    | xH =>
      allowed <- domain_compare false lo 0 ;;
      domain_case 331 [if allowed then 1%N else 0%N]
        (domain_return 332 [] (if allowed then Some 0%Z else None))
    | xO q | xI q =>
      clear <- product_odd_source zero ;;
      set <- product_odd_source one ;;
      domain_case 333 [if clear then 1%N else 0%N; if set then 1%N else 0%N]
        (if clear && set then domain_return 332 [] None else
          z <- domain_z DzDiv zero 2 ;;
          o <- domain_z DzDiv one 2 ;;
          threshold <- (if clear then up <- domain_z DzAdd lo 1 ;; domain_z DzDiv up 2
            else domain_z DzDiv lo 2) ;;
          smaller <- product_ceiling_source q z o threshold ;;
          domain_case 334 []
            (match smaller with
            | None => domain_return 332 [] None
            | Some value =>
              twice <- domain_z DzMul 2 value ;;
              out <- (if clear then (twice, []) else if set then domain_z DzAdd twice 1 else
                digit <- product_free_source lo value ;; domain_z DzAdd twice digit) ;;
              domain_return 332 [count_zencode out] (Some out)
            end))
    end).

Definition product_tnum_ceiling_source (w : width) (a : tnum) (lo : Z)
    : domain_run (option Z) :=
  tree <- product_tree_source w ;;
  z <- domain_zeros a ;;
  o <- domain_ones a ;; product_ceiling_source tree z o lo.

Definition product_tnum_not_source (w : width) (a : tnum) : domain_run tnum :=
  o <- domain_ones a ;;
  z <- domain_wrap w o ;;
  old_z <- domain_zeros a ;;
  new_o <- domain_wrap w old_z ;; domain_tnum z new_o.

Definition product_tnum_floor_source (w : width) (a : tnum) (hi : Z)
    : domain_run (option Z) :=
  opposite <- product_tnum_not_source w a ;;
  m <- domain_modulus w ;;
  upper <- domain_z DzSub m 1 ;;
  mirror <- domain_z DzSub upper hi ;;
  selected <- product_tnum_ceiling_source w opposite mirror ;;
  domain_case 335 []
    (match selected with
    | None => domain_return 332 [] None
    | Some value =>
      m2 <- domain_modulus w ;;
      upper2 <- domain_z DzSub m2 1 ;;
      out <- domain_z DzSub upper2 value ;;
      domain_return 332 [count_zencode out] (Some out)
    end).

Definition product_linear_source (w : width) (a : tnum) (lo hi : Z)
    : domain_run (option (Z * Z)) :=
  first <- product_tnum_ceiling_source w a lo ;;
  domain_case 336 []
    (match first with
    | Some first_value =>
      last <- product_tnum_floor_source w a hi ;;
      match last with
      | Some last_value =>
      ordered <- domain_compare false first_value last_value ;;
      domain_case 337 [if ordered then 1%N else 0%N]
        (domain_return 338 [] (if ordered then Some (first_value, last_value) else None))
      | None => domain_return 338 [] None
      end
    | None => domain_return 338 [] None
    end).

Definition product_arc_source (w : width) (a : tnum) (lo hi : Z)
    : domain_run (option (Z * Z)) :=
  ordered <- domain_compare false lo hi ;;
  domain_case 339 [if ordered then 1%N else 0%N]
    (if ordered then product_linear_source w a lo hi else
      m <- domain_modulus w ;;
      upper <- domain_z DzSub m 1 ;;
      first <- product_linear_source w a lo upper ;;
      second <- product_linear_source w a 0 hi ;;
      domain_case 340 []
        (match first, second with
        | Some (first_value, _), Some (_, last_value) =>
          domain_return 338 [] (Some (first_value, last_value))
        | Some bounds, None | None, Some bounds => domain_return 338 [] (Some bounds)
        | None, None => domain_return 338 [] None
        end)).

(** Generic pack bodies are executed at the actual indices, with repeated depth work. *)
Fixpoint product_pack_source (p : positive) (test : Z -> domain_run bool) : domain_run Z :=
  domain_case 341 [N.pos p]
    (match p with
    | xH => (0%Z, [])
    | xO q | xI q =>
      lower <- product_pack_source q test ;;
      first_depth <- product_depth_source q ;;
      set <- test first_depth ;;
      domain_case 342 [if set then 1%N else 0%N]
        (if set then
          second_depth <- product_depth_source q ;;
          (Z.setbit lower second_depth, [scalar_z 343 lower second_depth])
        else (lower, []))
    end).

Definition product_prefix_test_source (negated : bool) (lo hi index : Z) : domain_run bool :=
  first_power <- domain_z DzPow 2 index ;;
  first <- domain_z DzDiv lo first_power ;;
  second_power <- domain_z DzPow 2 index ;;
  second <- domain_z DzDiv hi second_power ;;
  equal <- domain_equal first second ;;
  bit <- domain_testbit lo index ;;
  let selected := if negated then negb bit else bit in
  (equal && selected,
    (if negated then [AuditCase 219 []] else []) ++ [AuditCase 220 []]).

Definition product_prefix_source (w : width) (lo hi : Z) : domain_run tnum :=
  first_tree <- product_tree_source w ;;
  z <- product_pack_source first_tree (product_prefix_test_source true lo hi) ;;
  second_tree <- product_tree_source w ;;
  o <- product_pack_source second_tree (product_prefix_test_source false lo hi) ;;
  domain_tnum z o.

Definition product_arc_bits_source (w : width) (a : tnum) (lo hi : Z) : domain_run tnum :=
  ordered <- domain_compare false lo hi ;;
  domain_case 344 [if ordered then 1%N else 0%N]
    (if ordered then prefix <- product_prefix_source w lo hi ;;
      domain_tnum_bits DzOr w a prefix else (a, [])).

(** Concrete exchange expands canonical bottom even when the retained result is nonbottom. *)
Definition product_bits_round_source (w : width) (input : tnum * wrapped)
    : domain_run (tnum * wrapped) :=
  let a := fst input in
  ignored <- domain_tell [AuditCase 345 []] ;;
  bottom <- domain_bottom w ;;
  ignored <- domain_tell [AuditConstruct 346 []; AuditConstruct 347 []] ;;
  empty <- domain_empty w a ;;
  domain_case 348 [if empty then 1%N else 0%N]
    (if empty then ((bottom, WBot), []) else
      normalized <- product_wrapped_norm_source w (snd input) ;;
      domain_case 349 []
        (match normalized with
        | WBot => ((bottom, WBot), [])
        | WFull => domain_return 347 [] (a, WFull)
        | WItv lo hi =>
          selected <- product_arc_source w a lo hi ;;
          domain_case 350 []
            (match selected with
            | None => ((bottom, WBot), [])
            | Some (first, last) =>
              refined <- product_arc_bits_source w a first last ;;
              domain_return 347 [count_zencode first; count_zencode last]
                (refined, WItv first last)
            end)
        end)).

Definition product_frame_weight (event : audit_event unit) : nat :=
  match event with
  | AuditArithmetic 328 [z] => S (audit_z_bits (count_zdecode z))
  | AuditArithmetic 343 [z; amount] =>
    audit_shift_weight (count_zdecode z) (count_zdecode amount)
  | _ => domain_frame_weight event
  end.

Definition product_work (events : audit_trace unit) : nat :=
  fold_right (fun event total => (product_frame_weight event + total)%nat) 0%nat events.

(** The concrete exchange erases to the existing bits/wrapped round without a checker premise. *)
Definition product_bits_round_source_erases_type : Prop := forall w input,
  fst (product_bits_round_source w input) = product_bits_round w input.

(** Every pack charges all repeated depth visits on its actual recursive path. *)
Definition product_pack_depth_bound_type : Prop := forall p negated lo hi,
  (audit_case_count 326 (snd (product_pack_source p
    (product_prefix_test_source negated lo hi))) <=
    2 * Pos.size_nat p * Pos.size_nat p)%nat.

(** Concrete whole-round work has a polynomial envelope in width and all raw integer fields. *)
Definition product_bits_round_source_bound_type : Prop := forall w a b,
  let raw := match b with WItv lo hi => (audit_z_bits lo + audit_z_bits hi)%nat
    | _ => 1%nat end in
  let size := (1 + Pos.to_nat w + audit_z_bits (zeros a) + audit_z_bits (ones a) + raw)%nat in
  (product_work (snd (product_bits_round_source w (a, b))) <=
    10000000 * (Pos.to_nat w + 1) * (Pos.to_nat w + 1) * (size + 1) * (size + 1))%nat.
```

## Galois.Domains.DomainsAuditReduce

Card: AUD-DR

Source destination: `theories/Domains/DomainsAuditReduce.v`.

```rocq
(** * Stable reduction candidate check

    This scratch file elaborates the exact generic exchange proposition types.
    For example, stable reduction preserves product concretization.
    Builds on: OrderProduct and DomainsNumeric. *)

From Stdlib Require Import NArith ZArith.
From Galois.Order Require Import OrderLattice OrderProduct OrderReduced.
From Galois.Bits Require Import BitsWord.
From Galois.Domains Require Import DomainsNumeric DomainsProduct.

(** * Exchange record and proposition types *)

Record audit_exchange (P Q : Type) : Type := AuditExchange {
  audit_exchange_step : width -> P * Q -> P * Q;
  audit_exchange_rank : width -> P * Q -> N
}.

Arguments audit_exchange_step {P Q}.
Arguments audit_exchange_rank {P Q}.

Record audit_exchange_laws {P Q} (D1 : word_domain P) (D2 : word_domain Q)
    (G1 : width -> P -> Z -> Prop) (G2 : width -> Q -> Z -> Prop)
    (exchange : audit_exchange P Q) : Prop := {
  audit_exchange_descends : forall w x,
    leb (product_lattice (plat D1 w) (plat D2 w))
      (audit_exchange_step exchange w x) x = true;
  audit_exchange_monotone : forall w x y,
    leb (product_lattice (plat D1 w) (plat D2 w)) x y = true ->
    leb (product_lattice (plat D1 w) (plat D2 w))
      (audit_exchange_step exchange w x) (audit_exchange_step exchange w y) = true;
  audit_exchange_gamma : forall w x z,
    product_pgamma G1 G2 w (audit_exchange_step exchange w x) z <->
      product_pgamma G1 G2 w x z;
  audit_exchange_progress : forall w x,
    leb (product_lattice (plat D1 w) (plat D2 w)) x
      (audit_exchange_step exchange w x) = false ->
    (audit_exchange_rank exchange w (audit_exchange_step exchange w x) <
      audit_exchange_rank exchange w x)%N
}.

(** The public binary loop performs the fixed exchange until stable or its rank fuel ends. *)
Fixpoint audit_reduce_loop {P Q} (D1 : word_domain P) (D2 : word_domain Q)
    (exchange : audit_exchange P Q) (w : width) (fuel : positive) (input : P * Q)
    : P * Q :=
  let tick x := let next := audit_exchange_step exchange w x in
    if leb (product_lattice (plat D1 w) (plat D2 w)) x next then x else next in
  if leb (product_lattice (plat D1 w) (plat D2 w)) input
      (audit_exchange_step exchange w input) then input else
  match fuel with
  | xH => tick input
  | xO p => audit_reduce_loop D1 D2 exchange w p
    (audit_reduce_loop D1 D2 exchange w p input)
  | xI p => tick (audit_reduce_loop D1 D2 exchange w p
    (audit_reduce_loop D1 D2 exchange w p input))
  end.

(** The concrete public reducer derives its fuel from the supplied exchange's actual entry rank. *)
Definition audit_reduce {P Q} (D1 : word_domain P) (D2 : word_domain Q)
    (exchange : audit_exchange P Q) (w : width) (input : P * Q) : P * Q :=
  audit_reduce_loop D1 D2 exchange w (N.succ_pos (audit_exchange_rank exchange w input)) input.

Definition audit_reduce_gamma_type : Prop :=
  forall P Q (D1 : word_domain P) (D2 : word_domain Q)
    (G1 : width -> P -> Z -> Prop) (G2 : width -> Q -> Z -> Prop)
    (exchange : audit_exchange P Q), audit_exchange_laws D1 D2 G1 G2 exchange ->
    forall w x z, product_pgamma G1 G2 w (audit_reduce D1 D2 exchange w x) z <->
      product_pgamma G1 G2 w x z.

Definition audit_reduce_stable_type : Prop :=
  forall P Q (D1 : word_domain P) (D2 : word_domain Q)
    (G1 : width -> P -> Z -> Prop) (G2 : width -> Q -> Z -> Prop)
    (exchange : audit_exchange P Q), audit_exchange_laws D1 D2 G1 G2 exchange ->
    forall w x, let y := audit_reduce D1 D2 exchange w x in
      leb (product_lattice (plat D1 w) (plat D2 w)) y
        (audit_exchange_step exchange w y) = true.

Definition audit_reduce_rank_type : Prop :=
  forall P Q (D1 : word_domain P) (D2 : word_domain Q)
    (G1 : width -> P -> Z -> Prop) (G2 : width -> Q -> Z -> Prop)
    (exchange : audit_exchange P Q), audit_exchange_laws D1 D2 G1 G2 exchange ->
    forall w x,
      leb (product_lattice (plat D1 w) (plat D2 w)) x
        (audit_exchange_step exchange w x) = false ->
      (audit_exchange_rank exchange w (audit_exchange_step exchange w x) <
        audit_exchange_rank exchange w x)%N.

Definition audit_reduce_word_laws_type : Prop :=
  forall P Q (D1 : word_domain P) (D2 : word_domain Q)
    (G1 : width -> P -> Z -> Prop) (G2 : width -> Q -> Z -> Prop)
    (exchange : audit_exchange P Q), word_laws D1 G1 -> word_laws D2 G2 ->
    audit_exchange_laws D1 D2 G1 G2 exchange ->
    word_laws (product_word_domain D1 D2 (audit_reduce D1 D2 exchange))
      (product_pgamma G1 G2).
```

## Galois.Domains.DomainsAuditReduceBits

Card: AUD-DR

Source destination: `theories/Domains/DomainsAuditReduceBits.v`.

```rocq
(** * Concrete selected exchange composition

    This file substitutes fixed library-owned bodies into the generic reduction's actual calls.
    For example, rank computation pays its own exchange before comparing both product components.
    Builds on: ReduceWhole, ProductWhole and DomainPrimitive. *)

From Stdlib Require Import List NArith ZArith Bool.
From Galois.Order Require Import OrderLattice OrderProduct.
From Galois.Bits Require Import BitsWord.
From Galois.Domains Require Import DomainsNumeric DomainsKnownBits DomainsWrapped DomainsProduct.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Domains Require Import DomainsAuditNumericCost.
From Galois.Domains Require Import DomainsAuditReduce.
From Galois.Domains Require Import DomainsAuditReduceSource.
From Galois.Domains Require Import DomainsAuditProductSource.
Import List.ListNotations.

Definition reduce_bits_rank (w : width) (input : tnum * wrapped) : N :=
  if leb (product_lattice (tnum_lattice w) (wrapped_lattice w)) input
      (product_bits_round w input) then 0%N else 1%N.

Definition reduce_bits_exchange : audit_exchange tnum wrapped :=
  AuditExchange tnum wrapped product_bits_round reduce_bits_rank.

(** The selected library exchange satisfies the generic laws unconditionally. *)
Definition reduce_bits_exchange_laws_type : Prop :=
  audit_exchange_laws known_bits_domain wrapped_domain tnum_gamma wrapped_gamma
    reduce_bits_exchange.

(** This selected plain reducer fixes the library dictionaries and exchange. *)
Definition audit_reduce_bits (w : width) (input : tnum * wrapped) : tnum * wrapped :=
  audit_reduce known_bits_domain wrapped_domain reduce_bits_exchange w input.

Definition reduce_bits_compare_source (w : width) (lhs rhs : tnum * wrapped)
    : domain_run bool :=
  let '(first, e1) := domain_order w (fst lhs) (fst rhs) in
  let '(second, e2) := product_wrapped_order_source w (snd lhs) (snd rhs) in
  (first && second, [AuditCase 360 []; AuditCase 360 []] ++ e1 ++
    [AuditCase 361 []; AuditCase 361 []] ++ e2 ++ [AuditCase 362 []]).

Definition reduce_bits_rank_source (w : width) (input : tnum * wrapped) : domain_run N :=
  let '(next, first) := product_bits_round_source w input in
  let '(stable, second) := reduce_bits_compare_source w input next in
  (if stable then 0%N else 1%N, first ++ second ++ [AuditCase 363 []]).

(** Every formerly generic library-owned call now has its fixed literal body cost. *)
Definition reduce_bits_call_work (call : reduce_call tnum wrapped) : nat :=
  match call with
  | ReduceRankCall w input _ => product_work (snd (reduce_bits_rank_source w input))
  | ReduceStepCall w input _ => product_work (snd (product_bits_round_source w input))
  | ReduceLeftCall w lhs rhs _ => domain_work (snd (domain_order w lhs rhs))
  | ReduceRightCall w lhs rhs _ => product_work (snd (product_wrapped_order_source w lhs rhs))
  end.

Definition audit_reduce_bits_source (w : width) (input : tnum * wrapped)
    : (tnum * wrapped) * audit_trace (reduce_call tnum wrapped) :=
  audit_reduce_source known_bits_domain wrapped_domain reduce_bits_exchange w input.

Definition reduce_bits_whole_work (events : audit_trace (reduce_call tnum wrapped)) : nat :=
  (reduce_library_work events + reduce_client_body_work reduce_bits_call_work events)%nat.

(** Concrete rank erasure uses both actual component comparisons without a client law. *)
Definition reduce_bits_rank_source_erases_type : Prop := forall w input,
  fst (reduce_bits_rank_source w input) = reduce_bits_rank w input.

(** The whole selected operation preserves the native rank-derived reducer's exact result pair. *)
Definition audit_reduce_bits_source_erases_type : Prop := forall w input,
  fst (audit_reduce_bits_source w input) =
    reduce_loop_reference known_bits_domain wrapped_domain reduce_bits_exchange w
      (N.succ_pos (reduce_bits_rank w input)) input.

(** The concrete observer erases to the selected plain library operation. *)
Definition audit_reduce_bits_plain_erases_type : Prop := forall w input,
  fst (audit_reduce_bits_source w input) = audit_reduce_bits w input.

(** Whole selected work includes the rank's exchange, all loop exchanges and both comparators. *)
Definition audit_reduce_bits_source_bound_type : Prop := forall w a b,
  let raw := match b with WItv lo hi => (audit_z_bits lo + audit_z_bits hi)%nat
    | _ => 1%nat end in
  let size := (1 + Pos.to_nat w + audit_z_bits (zeros a) + audit_z_bits (ones a) + raw)%nat in
  (reduce_bits_whole_work (snd (audit_reduce_bits_source w (a, b))) <=
    1000000000 * (Pos.to_nat w + 1) * (Pos.to_nat w + 1) *
      (size + 1) * (size + 1) * (size + 1) * (size + 1))%nat.
```

## Galois.Domains.DomainsAuditReduceSource

Card: AUD-DR

Source destination: `theories/Domains/DomainsAuditReduceSource.v`.

```rocq
(** * Generic rank-derived reduction source equations

    Calls retain the actual dictionary, exchange and rank operands of one reduction.
    For example, a stable loop still executes its terminal exchange and both comparisons.
    Builds on: ReduceCandidate, OrderProduct and NumericCostVocabulary. *)

From Stdlib Require Import List NArith PArith ZArith Bool.
From Galois.Order Require Import OrderLattice OrderProduct.
From Galois.Bits Require Import BitsWord.
From Galois.Domains Require Import DomainsNumeric.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Domains Require Import DomainsAuditReduce.
Import List.ListNotations.

(** Typed calls distinguish external dictionary bodies from the library loop's own work. *)
Inductive reduce_call (P Q : Type) : Type :=
  | ReduceRankCall (w : width) (input : P * Q) (output : N)
  | ReduceStepCall (w : width) (input output : P * Q)
  | ReduceLeftCall (w : width) (lhs rhs : P) (output : bool)
  | ReduceRightCall (w : width) (lhs rhs : Q) (output : bool).

Arguments ReduceRankCall {P Q}.
Arguments ReduceStepCall {P Q}.
Arguments ReduceLeftCall {P Q}.
Arguments ReduceRightCall {P Q}.

Definition reduce_compare_source {P Q} (D1 : word_domain P) (D2 : word_domain Q)
    (w : width) (lhs rhs : P * Q) : bool * audit_trace (reduce_call P Q) :=
  let first := leb (plat D1 w) (fst lhs) (fst rhs) in
  let second := leb (plat D2 w) (snd lhs) (snd rhs) in
  (first && second,
    [AuditCase 300 []; AuditCase 300 [];
     AuditCall (ReduceLeftCall w (fst lhs) (fst rhs) first);
     AuditCase 301 []; AuditCase 301 [];
     AuditCall (ReduceRightCall w (snd lhs) (snd rhs) second);
     AuditCase 302 [if first then 1%N else 0%N; if second then 1%N else 0%N]]).

Definition reduce_tick_source {P Q} (D1 : word_domain P) (D2 : word_domain Q)
    (exchange : audit_exchange P Q) (w : width) (input : P * Q)
    : (P * Q) * audit_trace (reduce_call P Q) :=
  let next := audit_exchange_step exchange w input in
  let '(stable, compared) := reduce_compare_source D1 D2 w input next in
  (if stable then input else next,
    AuditCall (ReduceStepCall w input next) :: compared ++
      [AuditCase 303 [if stable then 1%N else 0%N]]).

(** This equation retains repeated loop entry checks and the final odd-fuel tick. *)
Fixpoint reduce_loop_source {P Q} (D1 : word_domain P) (D2 : word_domain Q)
    (exchange : audit_exchange P Q) (w : width) (fuel : positive) (input : P * Q)
    : (P * Q) * audit_trace (reduce_call P Q) :=
  let next := audit_exchange_step exchange w input in
  let '(stable, compared) := reduce_compare_source D1 D2 w input next in
  let prefix := AuditCase 304 [N.pos fuel] ::
    AuditCall (ReduceStepCall w input next) :: compared ++
      [AuditCase 305 [if stable then 1%N else 0%N]] in
  if stable then (input, prefix) else
  match fuel with
  | xH => let '(out, body) := reduce_tick_source D1 D2 exchange w input in
    (out, prefix ++ AuditCase 306 [1%N] :: body)
  | xO p =>
    let '(mid, first) := reduce_loop_source D1 D2 exchange w p input in
    let '(out, second) := reduce_loop_source D1 D2 exchange w p mid in
    (out, prefix ++ AuditCase 306 [N.pos fuel] :: first ++ second)
  | xI p =>
    let '(mid1, first) := reduce_loop_source D1 D2 exchange w p input in
    let '(mid2, second) := reduce_loop_source D1 D2 exchange w p mid1 in
    let '(out, third) := reduce_tick_source D1 D2 exchange w mid2 in
    (out, prefix ++ AuditCase 306 [N.pos fuel] :: first ++ second ++ third)
  end.

(** Entry rank, binary successor fuel, loop, and returned endpoint use the same execution. *)
Definition audit_reduce_source {P Q} (D1 : word_domain P) (D2 : word_domain Q)
    (exchange : audit_exchange P Q) (w : width) (input : P * Q)
    : (P * Q) * audit_trace (reduce_call P Q) :=
  let rank := audit_exchange_rank exchange w input in
  let fuel := N.succ_pos rank in
  let '(out, body) := reduce_loop_source D1 D2 exchange w fuel input in
  (out, [AuditCall (ReduceRankCall w input rank); AuditArithmetic 307 [rank]] ++ body).

(** This reference is the source's ordinary uninstrumented binary loop. *)
Fixpoint reduce_loop_reference {P Q} (D1 : word_domain P) (D2 : word_domain Q)
    (exchange : audit_exchange P Q) (w : width) (fuel : positive) (input : P * Q)
    : P * Q :=
  let tick x := let next := audit_exchange_step exchange w x in
    if leb (product_lattice (plat D1 w) (plat D2 w)) x next then x else next in
  if leb (product_lattice (plat D1 w) (plat D2 w)) input
      (audit_exchange_step exchange w input) then input else
  match fuel with
  | xH => tick input
  | xO p => reduce_loop_reference D1 D2 exchange w p
    (reduce_loop_reference D1 D2 exchange w p input)
  | xI p => tick (reduce_loop_reference D1 D2 exchange w p
    (reduce_loop_reference D1 D2 exchange w p input))
  end.

(** Erasure preserves both result components of the actual rank-derived reducer. *)
Definition audit_reduce_source_erases_type : Prop := forall P Q
    (D1 : word_domain P) (D2 : word_domain Q) (exchange : audit_exchange P Q) w input,
  fst (audit_reduce_source D1 D2 exchange w input) =
    reduce_loop_reference D1 D2 exchange w (N.succ_pos (audit_exchange_rank exchange w input))
      input.

Definition reduce_step_calls {P Q} (events : audit_trace (reduce_call P Q)) : nat :=
  fold_right (fun event total =>
    match event with AuditCall (ReduceStepCall _ _ _) => S total | _ => total end) 0%nat events.

(** Every source execution has at most three rank-plus-one exchange checks. *)
Definition audit_reduce_source_calls_type : Prop := forall P Q
    (D1 : word_domain P) (D2 : word_domain Q) (exchange : audit_exchange P Q) w input,
  let '(_, events) := audit_reduce_source D1 D2 exchange w input in
  (reduce_step_calls events <= 3 * N.to_nat (N.succ (audit_exchange_rank exchange w input)) /\
    audit_work events <= 40 * N.to_nat (N.succ (audit_exchange_rank exchange w input)) + 2)%nat.

(** Client body budgets attach to actual typed calls, never to a desired whole-loop inequality. *)
Definition reduce_client_body_work {P Q} (body_work : reduce_call P Q -> nat)
    (events : audit_trace (reduce_call P Q)) : nat :=
  fold_right (fun event total =>
    match event with AuditCall call => (body_work call + total)%nat | _ => total end) 0%nat events.

(** Library-owned work excludes client bodies but includes every call and successor operand. *)
Definition reduce_library_work {P Q} (events : audit_trace (reduce_call P Q)) : nat :=
  fold_right (fun event total =>
    ((match event with
    | AuditArithmetic 307 [rank] => S (audit_z_bits (Z.of_N rank))
    | _ => 1%nat
    end) + total)%nat) 0%nat events.

(** The whole model composes the library budget and the actual external body executions. *)
Definition audit_reduce_source_bound_type : Prop := forall P Q
    (D1 : word_domain P) (D2 : word_domain Q) (exchange : audit_exchange P Q) w input
    (body_work : reduce_call P Q -> nat),
  let '(_, events) := audit_reduce_source D1 D2 exchange w input in
  let rank := audit_exchange_rank exchange w input in
  (reduce_library_work events + reduce_client_body_work body_work events <=
    50 * N.to_nat (N.succ rank) + 2 * audit_z_bits (Z.of_N rank) +
      reduce_client_body_work body_work events)%nat.

(** The reduction observer preserves the fixed public rank-derived loop. *)
Definition reduce_plain_erases_type : Prop := forall P Q D1 D2
    (exchange : audit_exchange P Q) w input,
  fst (audit_reduce_source D1 D2 exchange w input) = audit_reduce D1 D2 exchange w input.
```

## Galois.Domains.DomainsAuditTransfer

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransfer.v`.

```rocq
(** * Transfer statement check

    This scratch file elaborates the selected transfer and its obligations.
    For example, zero divisors retain the old transfer.
    Builds on: DomainsSignedBoundsDomain. *)

From Stdlib Require Import List NArith PArith ZArith Bool.
From Galois.Order Require Import OrderLattice.
From Galois.Bits Require Import BitsWord BitsOp.
From Galois.Domains Require Import DomainsNumeric DomainsSignedBounds DomainsKnownBits
  DomainsWrapped DomainsSignedBoundsDomain.
Import List.ListNotations.

(** * Candidate definitions and proposition types *)

Definition audit_div_one_guard (o : op) (wps : list (width * signed_bounds))
    (rw : width) : bool :=
  match o, wps with
  | bvsdiv, [(wa, _); (wb, b)] =>
    Pos.leb 2 rw && Pos.eqb wa rw && Pos.eqb wb rw &&
    leb (signed_bounds_lattice rw) b (signed_bounds_const rw 1) &&
    negb (leb (signed_bounds_lattice rw) b (bot (signed_bounds_lattice rw)))
  | _, _ => false
  end.

Definition audit_div_one_forward (o : op) (wps : list (width * signed_bounds))
    (rw : width) : signed_bounds :=
  if audit_div_one_guard o wps rw then
    match wps with
    | [(_, a); _] => a
    | _ => pforward signed_bounds_domain o wps rw
    end
  else pforward signed_bounds_domain o wps rw.

Definition audit_div_one_domain : word_domain signed_bounds :=
  {| plat := plat signed_bounds_domain;
     ptop := ptop signed_bounds_domain;
     pconst := pconst signed_bounds_domain;
     pforward := audit_div_one_forward;
     passume := passume signed_bounds_domain;
     pmeet := pmeet signed_bounds_domain |}.

Definition audit_transfer_sound_type : Prop := forall o wps ys rw z,
  Forall2 (payload_sound signed_bounds_gamma) wps ys ->
  eval_op o ys = Some (rw, z) ->
  signed_bounds_gamma rw (audit_div_one_forward o wps rw) z.

Definition audit_div_one_fallback_type : Prop := forall o wps rw,
  audit_div_one_guard o wps rw = false ->
  audit_div_one_forward o wps rw = pforward signed_bounds_domain o wps rw.

Definition audit_div_one_refines_type : Prop := forall o wps rw,
  leb (signed_bounds_lattice rw) (audit_div_one_forward o wps rw)
    (pforward signed_bounds_domain o wps rw) = true.

Definition audit_div_one_laws_type : Prop := word_laws audit_div_one_domain signed_bounds_gamma.

Definition audit_transfer_shapes_type : Prop :=
  (forall o wps rw, audit_div_one_guard o wps rw = false ->
    audit_div_one_forward o wps rw = pforward signed_bounds_domain o wps rw) /\
  (forall o args rw, (forall a b, o = bvsdiv -> args = [(rw,a); (rw,b)] -> False) ->
    audit_div_one_forward o args rw = pforward signed_bounds_domain o args rw) /\
  (forall a b,
    audit_div_one_forward bvsdiv [(1%positive,a); (1%positive,b)] 1%positive =
      pforward signed_bounds_domain bvsdiv [(1%positive,a); (1%positive,b)] 1%positive) /\
  (forall w a,
    audit_div_one_forward bvsdiv [(w,a); (w,signed_bounds_const w 0%Z)] w =
      pforward signed_bounds_domain bvsdiv [(w,a); (w,signed_bounds_const w 0%Z)] w) /\
  (forall o args rw, o <> bvsdiv ->
    audit_div_one_forward o args rw = pforward signed_bounds_domain o args rw) /\
  (forall w t z, is_word w z -> tnum_gamma w t z ->
    signed_bounds_gamma w (sb_from_components w t WFull) z).

Definition audit_dividend : signed_bounds := sb_lift 4%positive (Tnum 1 0) 0 2.
Definition audit_divisor : signed_bounds := signed_bounds_const 4%positive 1.
Definition audit_existing_division : signed_bounds :=
  pforward signed_bounds_domain bvsdiv
    [(4%positive, audit_dividend); (4%positive, audit_divisor)] 4%positive.

Definition audit_div_one_strict_type : Prop :=
  let input := [(4%positive, audit_dividend); (4%positive, audit_divisor)] in
  leb (signed_bounds_lattice 4%positive) (signed_bounds_const 4%positive 1)
    audit_existing_division = true /\
  leb (signed_bounds_lattice 4%positive) (signed_bounds_const 4%positive 1)
    (audit_div_one_forward bvsdiv input 4%positive) = false.
```

## Galois.Domains.DomainsAuditTransferBounds

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransferBounds.v`.

```rocq
(** * Whole transfer and dispatcher theorem types
    Bounds depend only on raw inputs, including all numeric widths and unary operator indices.
    Builds on: NumericDimensions and TransferWhole. *)
From Stdlib Require Import List NArith PArith ZArith.
From Galois.Bits Require Import BitsWord BitsOp.
From Galois.Domains Require Import DomainsKnownBits DomainsInterval DomainsWrapped
  DomainsSignedBounds.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Domains Require Import DomainsAuditNumericCost.
From Galois.Domains Require Import DomainsAuditKnownBitsSource.
From Galois.Domains Require Import DomainsAuditNumericDimensions.
From Galois.Domains Require Import DomainsAuditTransferWord.
From Galois.Domains Require Import DomainsAuditTransferInterval.
From Galois.Domains Require Import DomainsAuditProductSource.
From Galois.Domains Require Import DomainsAuditTransferWrapped.
From Galois.Domains Require Import DomainsAuditWidenSource.
From Galois.Domains Require Import DomainsAuditMulSource.
From Galois.Domains Require Import DomainsAuditMulDispatch.
From Galois.Domains Require Import DomainsAuditTransferSource.
Import ListNotations.
Definition numeric_bound_dimension b := match b with Fin z => S(audit_z_bits z) | _ => 1%nat end.
Definition numeric_interval_dimension a := match a with IBot => 1%nat
 | Itv lo hi => (1+numeric_bound_dimension lo+numeric_bound_dimension hi)%nat end.
Definition numeric_wrapped_dimension a := match a with WItv lo hi => (1+audit_z_bits
  lo+audit_z_bits hi)%nat | _ => 1%nat end.
Definition numeric_word_dimension o (args : list word) :=
 (1+numeric_operator_dimension o+fold_right(fun wz n => (1+Pos.to_nat(fst wz)+audit_z_bits(snd
   wz)+n)%nat) 0%nat args)%nat.
Definition numeric_iv_dimension o (args : list(width*interval)) rw :=
 (1+numeric_operator_dimension o+Pos.to_nat rw+fold_right(fun wa n => (1+Pos.to_nat(fst
   wa)+numeric_interval_dimension(snd wa)+n)%nat) 0%nat args)%nat.
Definition numeric_wr_dimension o (args : list(width*wrapped)) rw :=
 (1+numeric_operator_dimension o+Pos.to_nat rw+fold_right(fun wa n => (1+Pos.to_nat(fst
   wa)+numeric_wrapped_dimension(snd wa)+n)%nat) 0%nat args)%nat.
Definition numeric_sb_dimension o (args : list(width*signed_bounds)) rw :=
 (1+numeric_operator_dimension o+Pos.to_nat rw+fold_right(fun wa n =>
 (1+Pos.to_nat(fst wa)+widen_half_size(sb_zero(snd wa))+widen_half_size(sb_one(snd wa))+n)%nat)
   0%nat args)%nat.
Definition word_eval_source_bound_type : Prop := forall o args,
 (word_source_work(snd(word_eval_source o args)) <= numeric_envelope(numeric_word_dimension o
   args))%nat.
Definition iv_forward_source_bound_type : Prop := forall o args rw,
 (iv_work(snd(iv_forward o args rw)) <= numeric_envelope(numeric_iv_dimension o args rw))%nat.
Definition wr_forward_source_bound_type : Prop := forall o args rw,
 (wr_work(snd(wr_forward o args rw)) <= numeric_envelope(numeric_wr_dimension o args rw))%nat.
Definition sb_forward_source_bound_type : Prop := forall o args rw,
 (transfer_work(snd(sb_forward_source o args rw)) <= numeric_envelope(numeric_sb_dimension o args
   rw))%nat.
Definition transfer_source_bound_type : Prop := forall o args rw,
 (transfer_work(snd(transfer_forward_source o args rw)) <= numeric_envelope(numeric_sb_dimension o
   args rw))%nat.
Definition transfer_guard_source_bound_type : Prop := forall o args rw,
 (transfer_work(snd(transfer_guard_source o args rw)) <= numeric_envelope(numeric_sb_dimension o
   args rw))%nat.
Definition transfer_whole_execution_type : Prop := forall o args rw,
 exists result trace, transfer_forward_source o args rw=(result,trace) /\
 (transfer_work trace <= numeric_envelope(numeric_sb_dimension o args rw))%nat.
Definition iv_source_total_type : Prop := forall o args rw, exists r t, iv_forward o args rw=(r,t).
Definition iv_source_unique_type : Prop := forall o args rw r1 t1 r2 t2,
 iv_forward o args rw=(r1,t1) -> iv_forward o args rw=(r2,t2) -> r1=r2 /\ t1=t2.
Definition wr_source_total_type : Prop := forall o args rw, exists r t, wr_forward o args rw=(r,t).
Definition wr_source_unique_type : Prop := forall o args rw r1 t1 r2 t2,
 wr_forward o args rw=(r1,t1) -> wr_forward o args rw=(r2,t2) -> r1=r2 /\ t1=t2.
```

## Galois.Domains.DomainsAuditTransferInterval

Card: AUD-DT-INTERVAL

Source destination: `theories/Domains/DomainsAuditTransferInterval.v`.

```rocq
(** * Literal interval transfer source model
    Fixed local branch allowance 100; every integer operation and nested call is separate.
    Builds on: WordForwardWhole, KnownBitsWhole and DomainsInterval. *)
From Stdlib Require Import List NArith ZArith Bool.
From Galois.Order Require Import OrderLattice.
From Galois.Bits Require Import BitsWord BitsFun BitsOp.
From Galois.Domains Require Import DomainsInterval.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Domains Require Import DomainsAuditNumericCost.
From Galois.Domains Require Import DomainsAuditKnownBitsSource.
From Galois.Domains Require Import DomainsAuditTransferWord.
Import ListNotations.
Definition iv_mark {A} (r : domain_run A) := domain_case 520 [] r.
Definition iv_finite (a : interval) := iv_mark (interval_finite a, []).
Definition iv_make lo hi : domain_run interval := domain_return 521 [] (Itv (Fin lo) (Fin hi)).
Definition iv_top w := m <- domain_modulus w ;; hi <- domain_z DzSub m 1 ;; iv_make 0 hi.
Definition iv_bound_le a b : domain_run bool := iv_mark (
 match a,b with NegInf,_ | _,PosInf => (true,[]) | Fin x,Fin y => domain_compare false x y | _,_ =>
   (false,[]) end).
Definition iv_bound_pick (maximum : bool) a b := yes <- iv_bound_le a b ;;
 domain_return 522 [] (if yes then if maximum then b else a else if maximum then a else b).
Definition iv_meet a b := iv_mark (match a,b with
 | Itv l h,Itv l' h' => lo <- iv_bound_pick true l l' ;; hi <- iv_bound_pick false h h' ;;
   ok <- (match lo,hi with PosInf,_ | _,NegInf => (false,[]) | _,_ => iv_bound_le lo hi end) ;;
   domain_return 523 [] (if ok then Itv lo hi else IBot)
 | _,_ => (IBot,[]) end).
Definition iv_join a b := iv_mark (match a,b with
 | IBot,_ => (b,[]) | _,IBot => (a,[]) | Itv l h,Itv l' h' =>
 lo <- iv_bound_pick false l l' ;; hi <- iv_bound_pick true h h' ;; domain_return 523 [] (Itv lo
   hi) end).
Definition iv_checked w lo hi := iv_mark (
 first <- domain_compare false 0 lo ;; m <- domain_modulus w ;;
 second <- domain_compare true hi m ;;
 if first && second then iv_make lo hi else iv_top w).
Definition iv_add w a b := iv_mark (aa <- iv_finite a ;; match aa with
 | Some(la,ha) => bb <- iv_finite b ;; match bb with
 | Some(lb,hb) =>
 lo <- domain_z DzAdd la lb ;; hi <- domain_z DzAdd ha hb ;; iv_checked w lo hi | _ => iv_top w end
 | _ => iv_top w end).
Definition iv_sub w a b := iv_mark (aa <- iv_finite a ;; match aa with
 | Some(la,ha) => bb <- iv_finite b ;; match bb with
 | Some(lb,hb) =>
 lo <- domain_z DzSub la hb ;; hi <- domain_z DzSub ha lb ;; iv_checked w lo hi | _ => iv_top w end
 | _ => iv_top w end).
Definition iv_add_mod w a b := iv_mark (aa <- iv_finite a ;; match aa with
 | Some(la,ha) => bb <- iv_finite b ;; match bb with
 | Some(lb,hb) =>
 m <- domain_modulus w ;; lo <- domain_z DzAdd la lb ;; first <- domain_compare false m lo ;;
 hi <- domain_z DzAdd ha hb ;; m2 <- domain_modulus w ;; twice <- domain_z DzMul 2 m2 ;;
 second <- domain_compare true hi twice ;;
 if first && second then
 l <- domain_z DzAdd la lb ;; ml <- domain_modulus w ;; low <- domain_z DzSub l ml ;;
 h <- domain_z DzAdd ha hb ;; mh <- domain_modulus w ;; high <- domain_z DzSub h mh ;; iv_checked w
   low high
 else iv_add w a b | _ => iv_top w end
 | _ => iv_top w end).
Definition iv_mul w a b := iv_mark (aa <- iv_finite a ;; match aa with
 | Some(la,ha) => bb <- iv_finite b ;; match bb with
 | Some(lb,hb) =>
 first <- domain_compare false 0 la ;; second <- domain_compare false 0 lb ;;
 if first && second then lo <- domain_z DzMul la lb ;; hi <- domain_z DzMul ha hb ;; iv_checked w
   lo hi else iv_top w
 | _ => iv_top w end
 | _ => iv_top w end).
Definition iv_neg w a := iv_mark (aa <- iv_finite a ;; match aa with Some(lo,hi) =>
 zero <- domain_equal hi 0 ;; if zero then iv_make 0 0 else
 positive <- domain_compare true 0 lo ;; if positive then
 ml <- domain_modulus w ;; low <- domain_z DzSub ml hi ;;
 mh <- domain_modulus w ;; high <- domain_z DzSub mh lo ;; iv_checked w low high else iv_top w
 | None => iv_top w end).
Definition iv_not w a := iv_mark (aa <- iv_finite a ;; match aa with Some(lo,hi) =>
 ml <- domain_modulus w ;; lm <- domain_z DzSub ml 1 ;; low <- domain_z DzSub lm hi ;;
 mh <- domain_modulus w ;; hm <- domain_z DzSub mh 1 ;; high <- domain_z DzSub hm lo ;; iv_checked
   w low high
 | None => iv_top w end).
Definition iv_and w a b := aa <- iv_finite a ;; match aa with
 | Some(_,ha) => bb <- iv_finite b ;; match bb with
 | Some(_,hb) => hi <- domain_z DzMin ha hb ;; iv_checked w 0 hi | _ => iv_top w end
 | _ => iv_top w end.
Definition iv_mask hi := zero <- domain_equal hi 0 ;; if zero then (0%Z,[]) else
 lg <- kb_unary 501 Z.log2 hi ;; amount <- domain_z DzAdd lg 1 ;; kb_unary 503 Z.ones amount.
Definition iv_or w a b := aa <- iv_finite a ;; match aa with
 | Some(_,ha) => bb <- iv_finite b ;; match bb with
 | Some(_,hb) => hi <- domain_z DzMax ha hb ;; mask <- iv_mask hi ;; iv_checked w 0 mask | _ =>
   iv_top w end
 | _ => iv_top w end.
Definition iv_udiv w a b := iv_mark (aa <- iv_finite a ;; match aa with
 | Some(la,ha) => bb <- iv_finite b ;; match bb with
 | Some(lb,hb) =>
 first <- domain_compare false 0 la ;; second <- domain_compare true 0 lb ;;
 if first && second then lo <- domain_z DzDiv la hb ;; hi <- domain_z DzDiv ha lb ;; iv_checked w
   lo hi else
 p <- domain_compare false 0 la ;; z <- domain_equal lb 0 ;; pos <- domain_compare true 0 hb ;;
 if p && z && pos then lo <- domain_z DzDiv la hb ;; m <- domain_modulus w ;; hi <- domain_z DzSub
   m 1 ;; iv_checked w lo hi else
 zl <- domain_equal lb 0 ;; zh <- domain_equal hb 0 ;;
 if zl && zh then ml <- domain_modulus w ;; lo <- domain_z DzSub ml 1 ;;
 mh <- domain_modulus w ;; hi <- domain_z DzSub mh 1 ;; iv_make lo hi else iv_top w
 | _ => iv_top w end
 | _ => iv_top w end).
Definition iv_urem w a b := iv_mark (aa <- iv_finite a ;; match aa with
 | Some(la,ha) => bb <- iv_finite b ;; match bb with
 | Some(lb,hb) =>
 first <- domain_compare false 0 la ;; second <- domain_compare true 0 lb ;;
 ql <- domain_z DzDiv la hb ;; qh <- domain_z DzDiv ha lb ;; same <- domain_equal ql qh ;;
 if first && second && same then q <- domain_z DzDiv la hb ;;
 lp <- domain_z DzMul q hb ;; lo <- domain_z DzSub la lp ;;
 hp <- domain_z DzMul q lb ;; hi <- domain_z DzSub ha hp ;; iv_checked w lo hi else
 positive <- domain_compare true 0 lb ;;
 hi <- (if positive then pred <- domain_z DzSub hb 1 ;; domain_z DzMin ha pred else (ha,[])) ;;
   iv_checked w 0 hi
 | _ => iv_top w end
 | _ => iv_top w end).
Definition iv_shift (left : bool) w a b := iv_mark (aa <- iv_finite a ;; match aa with
 | Some(la,ha) => bb <- iv_finite b ;; match bb with
 | Some(lb,hb) =>
 first <- domain_compare false 0 la ;; second <- domain_compare false 0 lb ;; third <-
   domain_compare true hb (Z.pos w) ;;
 if first && second && third then
 pl <- domain_z DzPow 2 (if left then lb else hb) ;;
 lo <- domain_z (if left then DzMul else DzDiv) la pl ;;
 ph <- domain_z DzPow 2 (if left then hb else lb) ;;
 hi <- domain_z (if left then DzMul else DzDiv) ha ph ;; iv_checked w lo hi else iv_top w
 | _ => iv_top w end
 | _ => iv_top w end).
Definition iv_concat rw lw a b := aa <- iv_finite a ;; match aa with
 | Some(la,ha) => bb <- iv_finite b ;; match bb with
 | Some(lb,hb) => ml <- domain_modulus lw ;; lp <- domain_z DzMul la ml ;; lo <- domain_z DzAdd lp
   lb ;;
 mh <- domain_modulus lw ;; hp <- domain_z DzMul ha mh ;; hi <- domain_z DzAdd hp hb ;; iv_checked
   rw lo hi
 | _ => iv_top rw end
 | _ => iv_top rw end.
Definition iv_rewrap rw a := aa <- iv_finite a ;; match aa with Some(lo,hi) => iv_checked rw lo hi
  | _ => iv_top rw end.
Definition iv_truth decision := domain_return 524 [] (interval_truth decision).
Definition iv_bool_not a := aa <- iv_finite a ;; match aa with Some(lo,hi) =>
 lz <- domain_equal lo 0 ;; hz <- domain_equal hi 0 ;; if lz && hz then iv_truth (Some true) else
 lo1 <- domain_equal lo 1 ;; hi1 <- domain_equal hi 1 ;; iv_truth (if lo1 && hi1 then Some false
   else None)
 | _ => iv_truth None end.
Definition iv_compare (strict : bool) a b := aa <- iv_finite a ;; match aa with
 | Some(la,ha) => bb <- iv_finite b ;; match bb with
 | Some(lb,hb) => yes <- domain_compare strict ha lb ;; if yes then iv_truth (Some true) else
 no <- domain_compare (negb strict) hb la ;; iv_truth (if no then Some false else None)
 | _ => iv_truth None end
 | _ => iv_truth None end.
Definition iv_eq a b := aa <- iv_finite a ;; match aa with
 | Some(la,ha) => bb <- iv_finite b ;; match bb with
 | Some(lb,hb) => l <- domain_compare true ha lb ;; r <- domain_compare true hb la ;;
 if l || r then iv_truth (Some false) else
 x <- domain_equal la ha ;; y <- domain_equal lb hb ;; z <- domain_equal la lb ;;
 iv_truth (if x && y && z then Some true else None) | _ => iv_truth None end
 | _ => iv_truth None end.
Definition iv_signed w a := aa <- iv_finite a ;; match aa with Some(lo,hi) =>
 h <- kb_half w ;; below <- domain_compare true hi h ;; if below then (Some(lo,hi),[]) else
 h2 <- kb_half w ;; above <- domain_compare false h2 lo ;; if above then
 ml <- domain_modulus w ;; low <- domain_z DzSub lo ml ;;
 mh <- domain_modulus w ;; high <- domain_z DzSub hi mh ;; domain_return 525 [] (Some(low,high))
   else (None,[])
 | _ => (None,[]) end.
Definition iv_sign w a := aa <- iv_finite a ;; match aa with Some(lo,hi) =>
 h <- kb_half w ;; below <- domain_compare true hi h ;; if below then (Some false,[]) else
 h2 <- kb_half w ;; above <- domain_compare false h2 lo ;; (if above then Some true else None,[])
 | _ => (None,[]) end.
Definition iv_sext rw w a := signed <- iv_signed w a ;; match signed with Some(lo,hi) =>
 negative <- domain_compare true hi 0 ;; if negative then
 ml <- domain_modulus rw ;; low <- domain_z DzAdd ml lo ;;
 mh <- domain_modulus rw ;; high <- domain_z DzAdd mh hi ;; iv_checked rw low high else
 positive <- domain_compare false 0 lo ;; if positive then iv_checked rw lo hi else iv_top rw
 | _ => iv_top rw end.
Definition iv_signed_compare w strict a b := aa <- iv_signed w a ;; match aa with
 | Some(la,ha) => bb <- iv_signed w b ;; match bb with
 | Some(lb,hb) => yes <- domain_compare strict ha lb ;;
 if yes then iv_truth (Some true) else no <- domain_compare (negb strict) hb la ;; iv_truth (if no
   then Some false else None)
 | _ => iv_truth None end
 | _ => iv_truth None end.
Definition iv_sdiv (remainder : bool) w a b := sa <- iv_sign w a ;; match sa with
 | Some xa => sb <- iv_sign w b ;; match sb with
 | Some xb =>
 aa <- (if xa then iv_neg w a else (a,[])) ;; bb <- (if xb then iv_neg w b else (b,[])) ;;
 q <- (if remainder then iv_urem w aa bb else iv_udiv w aa bb) ;;
 if (if remainder then xa else xorb xa xb) then iv_neg w q else (q,[])
 | _ => iv_top w end
 | _ => iv_top w end.
Definition iv_mod_choice u candidate := aa <- iv_finite u ;; match aa with Some(lo,hi) =>
 positive <- domain_compare true 0 lo ;; if positive then (candidate,[]) else
 zero <- domain_equal hi 0 ;; if zero then iv_make 0 0 else z <- iv_make 0 0 ;; iv_join z candidate
 | _ => z <- iv_make 0 0 ;; iv_join z candidate end.
Definition iv_smod_base w a b := sa <- iv_sign w a ;; match sa with
 | Some xa => sb <- iv_sign w b ;; match sb with
 | Some xb =>
 aa <- (if xa then iv_neg w a else (a,[])) ;; bb <- (if xb then iv_neg w b else (b,[])) ;;
 u <- iv_urem w aa bb ;; candidate <- (match xa,xb with
 | false,false => (u,[]) | true,false => n <- iv_neg w u ;; iv_add_mod w n b
 | false,true => iv_add_mod w u b | true,true => iv_neg w u end) ;; iv_mod_choice u candidate
 | _ => iv_top w end
 | _ => iv_top w end.
Definition iv_smod w a b := sign <- iv_sign w b ;; match sign with
 Some false => bb <- iv_finite b ;; match bb with
 Some(lo,hi) => positive <- domain_compare true 0 lo ;; if positive then
 base <- iv_smod_base w a b ;; upper <- domain_z DzSub hi 1 ;; constraint <- iv_make 0 upper ;;
   iv_meet base constraint
 else iv_smod_base w a b | _ => iv_smod_base w a b end
 | _ => iv_smod_base w a b end.
Definition iv_ashr_small w a b := sign <- iv_sign w a ;; match sign with
 Some false => iv_shift false w a b | Some true => na <- iv_not w a ;; shifted <- iv_shift false w
   na b ;; iv_not w shifted
 | None => iv_top w end.
Definition iv_ashr w a b := sign <- iv_sign w a ;; match sign with
 Some sg => bb <- iv_finite b ;; match bb with
 Some(lo,hi) => saturated <- (if sg then m <- domain_modulus w ;; domain_z DzSub m 1 else (0%Z,[]))
   ;;
 small <- domain_compare true hi (Z.pos w) ;; if small then iv_ashr_small w a b else
 large <- domain_compare false (Z.pos w) lo ;; if large then iv_make saturated saturated else
 upper <- domain_z DzSub (Z.pos w) 1 ;; range <- iv_make lo upper ;; shifted <- iv_ashr_small w a
   range ;;
 sat <- iv_make saturated saturated ;; iv_join shifted sat | _ => iv_ashr_small w a b end
 | _ => iv_ashr_small w a b end.
Definition iv_clipped o (args : list(width*interval)) rw := iv_mark (match o,args with
 | bvnot,[(_,a)] => iv_not rw a | bvneg,[(_,a)] => iv_neg rw a
 | (bvclz|bvctz|bvpopcnt),[_] => iv_make 0 (Z.pos rw)
 | bvadd,[(_,a);(_,b)] => iv_add rw a b | bvsub,[(_,a);(_,b)] => iv_sub rw a b
 | bvmul,[(_,a);(_,b)] => iv_mul rw a b | bvudiv,[(_,a);(_,b)] => iv_udiv rw a b
 | bvurem,[(_,a);(_,b)] => iv_urem rw a b | bvsdiv,[(_,a);(_,b)] => iv_sdiv false rw a b
 | bvsrem,[(_,a);(_,b)] => iv_sdiv true rw a b | bvsmod,[(_,a);(_,b)] => iv_smod rw a b
 | bvand,[(_,a);(_,b)] => iv_and rw a b | (bvor|bvxor),[(_,a);(_,b)] => iv_or rw a b
 | bvshl,[(_,a);(_,b)] => iv_shift true rw a b | bvlshr,[(_,a);(_,b)] => iv_shift false rw a b
 | bvashr,[(_,a);(_,b)] => iv_ashr rw a b | bveq,[(_,a);(_,b)] => iv_eq a b
 | bvne,[(_,a);(_,b)] => q <- iv_eq a b ;; iv_bool_not q
 | bvult,[(_,a);(_,b)] => iv_compare true a b | bvule,[(_,a);(_,b)] => iv_compare false a b
 | bvslt,[(w,a);(_,b)] => iv_signed_compare w true a b | bvsle,[(w,a);(_,b)] => iv_signed_compare w
   false a b
 | bvite,[_;(_,a);(_,b)] => iv_join a b
 | (bvzext _|bvtrunc _),[(_,a)] => iv_rewrap rw a | bvsext _,[(w,a)] => iv_sext rw w a
 | bvconcat,[(_,a);(w,b)] => iv_concat rw w a b | _,_ => iv_top rw end).
Fixpoint iv_clip_list (args : list(width*interval)) : domain_run (list(width*interval)) := iv_mark (
 match args with [] => ([],[]) | (w,a)::rest => top <- iv_top w ;; clipped <- iv_meet a top ;;
 tail <- iv_clip_list rest ;; domain_return 526 [] ((w,clipped)::tail) end).
Fixpoint iv_empty_list (args : list(width*interval)) : domain_run bool := iv_mark (
 match args with [] => (false,[]) | (_,a)::rest =>
 let here := match a with IBot => true | _ => false end in
 later <- iv_empty_list rest ;; domain_return 527 [] (here || later) end).
Fixpoint iv_values (args : list(width*interval)) : domain_run (option(list word)) := iv_mark (
 match args with [] => (Some [],[]) | (w,a)::rest => aa <- iv_finite a ;;
 single <- (match aa with Some(lo,hi) => same <- domain_equal lo hi ;; (if same then Some lo else
   None,[]) | _ => (None,[]) end) ;;
 match single with
 | None => domain_return 528 [] None
 | Some z => later <- iv_values rest ;;
   domain_return 528 [] (match later with Some zs => Some((w,z)::zs) | None => None end)
 end end).
Definition iv_forward o args rw := iv_mark (clipped <- iv_clip_list args ;; empty <- iv_empty_list
  clipped ;;
 if empty then (IBot,[]) else if interval_point_fast o then values <- iv_values clipped ;;
 match values with Some xs => out <- word_eval_source o xs ;;
 (match out with Some(_,z) => Itv(Fin z)(Fin z) | None => IBot end,[])
 | None => iv_clipped o clipped rw end else iv_clipped o clipped rw).
Definition iv_frame_weight event := match event with AuditCase 520 _ => 100%nat | _ =>
  word_frame_weight event end.
Definition iv_work trace := fold_right (fun e n => (iv_frame_weight e+n)%nat) 0%nat trace.
Definition iv_forward_erases_type : Prop := forall o args rw, fst(iv_forward o args
  rw)=interval_forward o args rw.
Definition iv_helpers_erases_type : Prop :=
 (forall w a b, fst(iv_add_mod w a b)=interval_add_modular w a b) /\
 (forall w a b, fst(iv_smod w a b)=interval_smod w a b) /\
 (forall w a b, fst(iv_ashr w a b)=interval_ashr w a b).
```

## Galois.Domains.DomainsAuditTransferSource

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransferSource.v`.

```rocq
(** * Complete signed-bounds transfer source equations
    This composes strict guards, legacy all-operator fallback, every choice row and reconstruction.
    Builds on: WidenWhole, WrappedWhole and MulDispatch. *)
From Stdlib Require Import List NArith PArith ZArith Bool.
From Galois.Order Require Import OrderLattice.
From Galois.Bits Require Import BitsWord BitsOp.
From Galois.Domains Require Import DomainsNumeric DomainsKnownBits DomainsInterval
  DomainsSignedBounds DomainsWrapped DomainsSignedBoundsDomain.
From Galois.Domains Require Import DomainsAuditTransfer.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Domains Require Import DomainsAuditNumericCost.
From Galois.Domains Require Import DomainsAuditKnownBitsSource.
From Galois.Domains Require Import DomainsAuditTransferWord.
From Galois.Domains Require Import DomainsAuditTransferInterval.
From Galois.Domains Require Import DomainsAuditProductSource.
From Galois.Domains Require Import DomainsAuditTransferWrapped.
From Galois.Domains Require Import DomainsAuditWidenSource.
From Galois.Domains Require Import DomainsAuditMulSource.
From Galois.Domains Require Import DomainsAuditMulDispatch.
Import ListNotations.
Definition sb_mark {A} (r : domain_run A) := domain_case 560 [] r.
Definition sb_make z o := domain_return 561 [] (SignedBounds z o).
Definition sb_reduce_source w a := z <- widen_reduce w false (sb_zero a) ;;
 o <- widen_reduce w true (sb_one a) ;; sb_make z o.
Definition sb_join_half_source w sign a b := aa <- widen_reduce w sign a ;;
 bb <- widen_reduce w sign b ;; merged <- widen_merge w aa bb ;; widen_reduce w sign merged.
Definition sb_join_source w a b := z <- sb_join_half_source w false (sb_zero a)(sb_zero b) ;;
 o <- sb_join_half_source w true (sb_one a)(sb_one b) ;; sb_make z o.
Definition sb_lift_source w t lo hi := first <- widen_range t lo hi ;; second <- widen_range t lo
  hi ;;
 raw <- sb_make first second ;; sb_reduce_source w raw.
Definition sb_top_source w := m <- domain_modulus w ;; hi <- domain_z DzSub m 1 ;;
 ignored <- domain_tell [AuditConstruct 218 [0%N;0%N]] ;; sb_lift_source w tnum_top 0 hi.
Definition sb_const_source w z := t <- domain_const w z ;; lo <- domain_wrap w z ;;
 hi <- domain_wrap w z ;; sb_lift_source w t lo hi.
Definition sb_from_interval_source w t a := sb_mark (match a with IBot => sb_make SBEmpty SBEmpty
 | Itv lo hi => upper <- (match hi with Fin z => (z,[]) | _ => m <- domain_modulus w ;; domain_z
   DzSub m 1 end) ;;
 sb_lift_source w t (match lo with Fin z => z | _ => 0%Z end) upper end).
Definition sb_components_source w t arc := pieces <- wr_parts w arc ;;
 first <- sb_from_interval_source w t (fst pieces) ;; second <- sb_from_interval_source w t (snd
   pieces) ;;
 sb_join_source w first second.
Definition sb_order_source w a b := first <- widen_leb w false (sb_zero a)(sb_zero b) ;;
 second <- widen_leb w true (sb_one a)(sb_one b) ;; domain_return 562 [] (first && second).
Fixpoint sb_choice_prepend w h (tails : list(list(width*sb_half))) : domain_run
  (list(list(width*sb_half))) :=
 sb_mark (match tails with [] => ([],[]) | row::rest => first <- domain_return 563 [] ((w,h)::row)
   ;;
 later <- sb_choice_prepend w h rest ;; domain_return 564 [] (first::later) end).
Fixpoint sb_append_rows (first second : list(list(width*sb_half))) : domain_run
  (list(list(width*sb_half))) :=
 sb_mark (match first with [] => (second,[]) | row::rest => later <- sb_append_rows rest second ;;
   domain_return 564 [] (row::later) end).
Fixpoint sb_choices_source (args : list(width*signed_bounds)) : domain_run
  (list(list(width*sb_half))) := sb_mark (
 match args with [] => domain_return 564 [] [[]] | (w,a)::rest => tails <- sb_choices_source rest ;;
 reduced <- sb_reduce_source w a ;; first <- sb_choice_prepend w (sb_zero reduced) tails ;;
 second <- sb_choice_prepend w (sb_one reduced) tails ;; sb_append_rows first second end).
Fixpoint sb_bits_inputs (args : list(width*sb_half)) : domain_run (list(width*tnum)) := sb_mark (
 match args with [] => ([],[]) | (w,h)::rest => bits <- (match h with SBEmpty => domain_bottom w |
   SBRange t _ _ => (t,[]) end) ;;
 later <- sb_bits_inputs rest ;; domain_return 565 [] ((w,bits)::later) end).
Fixpoint sb_arc_inputs (args : list(width*sb_half)) : domain_run (list(width*wrapped)) := sb_mark (
 match args with [] => ([],[]) | (w,h)::rest => arc <- (match h with SBEmpty => (WBot,[]) | SBRange
   _ lo hi => wr_range w lo hi end) ;;
 later <- sb_arc_inputs rest ;; domain_return 566 [] ((w,arc)::later) end).
Definition sb_case_source o row rw := sb_mark (
 bit_args <- sb_bits_inputs row ;; bits <- mul_precise_forward_source o bit_args rw ;;
 arc_args <- sb_arc_inputs row ;; arc <- wr_forward o arc_args rw ;; sb_components_source rw bits
   arc).
Fixpoint sb_case_map_source o (rows : list(list(width*sb_half))) rw : domain_run (list
  signed_bounds) := sb_mark (
 match rows with [] => ([],[]) | row::rest => first <- sb_case_source o row rw ;;
 later <- sb_case_map_source o rest rw ;; domain_return 567 [] (first::later) end).
Fixpoint sb_join_all_source w (values : list signed_bounds) : domain_run signed_bounds := sb_mark (
 match values with [] => sb_make SBEmpty SBEmpty | first::rest => later <- sb_join_all_source w
   rest ;; sb_join_source w first later end).
Definition sb_forward_source o args rw := sb_mark (
 length <- word_length_source args ;;
 ignored <- domain_tell [AuditArithmetic 568 [N.of_nat length;3%N]] ;;
 if Nat.leb length 3 then choices <- sb_choices_source args ;;
 cases <- sb_case_map_source o choices rw ;; sb_join_all_source rw cases else sb_top_source rw).
Definition transfer_guard_source o (args : list(width*signed_bounds)) rw := sb_mark (
 match o,args with bvsdiv,[(wa,_);(wb,b)] =>
 width_ok <- domain_positive_le 2 rw ;; first <- domain_positive_eq wa rw ;; second <-
   domain_positive_eq wb rw ;;
 one <- sb_const_source rw 1 ;; included <- sb_order_source rw b one ;;
 bottom <- sb_make SBEmpty SBEmpty ;; empty <- sb_order_source rw b bottom ;;
 domain_return 569 [] (width_ok && first && second && included && negb empty)
 | _,_ => (false,[]) end).
Definition transfer_forward_source o args rw := guard <- transfer_guard_source o args rw ;;
 sb_mark (if guard then match args with [(_,a);_] => (a,[]) | _ => sb_forward_source o args rw end
 else sb_forward_source o args rw).
Definition transfer_frame_weight event := match event with
 | AuditCase 560 _ | AuditCase 530 _ | AuditCase 520 _ | AuditCase 510 _ => 100%nat
 | AuditArithmetic 568 [a;b] => S (Nat.min (N.to_nat a)(N.to_nat b))
 | AuditArithmetic 240 [z] | AuditArithmetic 243 [z] => audit_unary_conversion_weight (audit_z_bits
   (count_zdecode z))
 | AuditArithmetic 550 [a;b] | AuditArithmetic 551 [a;b] => (2+N.size_nat a+N.size_nat b)%nat
 | AuditCase 552 _ | AuditCase 553 _ => 100%nat
 | _ => word_frame_weight event end.
Definition transfer_work trace := fold_right (fun e n => (transfer_frame_weight e+n)%nat) 0%nat
  trace.
Definition sb_forward_source_erases_type : Prop := forall o args rw,
 fst(sb_forward_source o args rw)=pforward signed_bounds_domain o args rw.
Definition sb_choices_source_erases_type : Prop := forall args, fst(sb_choices_source
  args)=sb_choices args.
Definition transfer_guard_erases_type : Prop := forall o args rw,
 fst(transfer_guard_source o args rw)=
 match o,args with bvsdiv,[(wa,_);(wb,b)] => Pos.leb 2 rw && Pos.eqb wa rw && Pos.eqb wb rw &&
 leb (signed_bounds_lattice rw) b (signed_bounds_const rw 1) && negb(leb (signed_bounds_lattice rw)
   b (SignedBounds SBEmpty SBEmpty)) | _,_ => false end.
Definition transfer_fallback_type : Prop := forall o args rw, fst(transfer_guard_source o args
  rw)=false ->
 fst(transfer_forward_source o args rw)=pforward signed_bounds_domain o args rw.
Definition transfer_total_type : Prop := forall o args rw, exists r t, transfer_forward_source o
  args rw=(r,t).
Definition transfer_unique_type : Prop := forall o args rw r1 t1 r2 t2,
 transfer_forward_source o args rw=(r1,t1) -> transfer_forward_source o args rw=(r2,t2) -> r1=r2 /\
   t1=t2.
Definition transfer_choices_count_type : Prop := forall args,
 length(fst(sb_choices_source args))=Nat.pow 2 (length args).

(** The selected forward observer preserves the public division-by-one refinement exactly. *)
Definition transfer_forward_plain_erases_type : Prop := forall o args rw,
  fst (transfer_forward_source o args rw) = audit_div_one_forward o args rw.
```

## Galois.Domains.DomainsAuditTransferWord

Card: AUD-DT-WORD

Source destination: `theories/Domains/DomainsAuditTransferWord.v`.

```rocq
(** * Complete primitive word-evaluation source equations

    This file expands width checking, operand normalization and actual word operators.
    For example, signed modulus skips both final sign tests when the remainder is zero.
    Builds on: KnownBitsWhole, DomainPrimitive and BitsOp. *)

From Stdlib Require Import List NArith PArith ZArith Bool Arith.
From Galois.Bits Require Import BitsWord BitsFun BitsOp.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Domains Require Import DomainsAuditNumericCost.
From Galois.Domains Require Import DomainsAuditKnownBitsSource.
Import List.ListNotations.

Definition word_mark {A} (body : domain_run A) : domain_run A := domain_case 510 [] body.

Definition word_neg w x := negative <- domain_z DzSub 0 x ;; domain_wrap w negative.

Definition word_udiv (remainder : bool) w x y : domain_run Z := word_mark (
  first_divisor <- domain_wrap w y ;;
  zero <- domain_equal first_divisor 0 ;;
  if zero then
    if remainder then domain_wrap w x else m <- domain_modulus w ;; domain_z DzSub m 1
  else
    dividend <- domain_wrap w x ;;
    divisor <- domain_wrap w y ;; domain_z (if remainder then DzMod else DzDiv) dividend divisor).

Definition word_signed_div (remainder : bool) w x y : domain_run Z := word_mark (
  sx <- kb_msb w x ;;
  sy <- kb_msb w y ;;
  match sx, sy with
  | false, false => word_udiv remainder w x y
  | true, false => first <- word_neg w x ;;
    out <- word_udiv remainder w first y ;; word_neg w out
  | false, true => second <- word_neg w y ;;
    out <- word_udiv remainder w x second ;;
    if remainder then (out, []) else word_neg w out
  | true, true => first <- word_neg w x ;;
    second <- word_neg w y ;;
    out <- word_udiv remainder w first second ;;
    if remainder then word_neg w out else (out, [])
  end).

Definition word_smod w x y : domain_run Z := word_mark (
  sx1 <- kb_msb w x ;;
  first <- (if sx1 then word_neg w x else domain_wrap w x) ;;
  sy1 <- kb_msb w y ;;
  second <- (if sy1 then word_neg w y else domain_wrap w y) ;;
  value <- word_udiv true w first second ;;
  zero <- domain_equal value 0 ;;
  if zero then (value, []) else
  sx2 <- kb_msb w x ;;
  sy2 <- kb_msb w y ;;
  match sx2, sy2 with
  | false, false => (value, [])
  | true, false => negative <- word_neg w value ;;
    sum <- domain_z DzAdd negative y ;; domain_wrap w sum
  | false, true => sum <- domain_z DzAdd value y ;; domain_wrap w sum
  | true, true => word_neg w value
  end).

Definition word_clz w x : domain_run Z := word_mark (
  first <- domain_wrap w x ;;
  zero <- domain_equal first 0 ;;
  if zero then (Z.pos w, []) else
    predecessor <- domain_z DzSub (Z.pos w) 1 ;;
    second <- domain_wrap w x ;;
    bits <- kb_unary 501 Z.log2 second ;; domain_z DzSub predecessor bits).

Fixpoint word_sequence_source (count start : nat) : domain_run (list nat) := word_mark (
  match count with
  | O => ([], [])
  | S rest => suffix <- word_sequence_source rest (S start) ;;
    domain_return 511 [] (start :: suffix)
  end).

Fixpoint word_pop_filter w x (indices : list nat) : domain_run (list nat) := word_mark (
  match indices with
  | [] => ([], [])
  | index :: rest =>
    value <- domain_wrap w x ;;
    let bit_index := Z.of_nat index in
    let '(set, tested) := domain_testbit value bit_index in
    let '(tail, body) := word_pop_filter w x rest in
    (if set then index :: tail else tail,
      AuditArithmetic 505 [N.of_nat index] :: tested ++ body ++
        (if set then [AuditConstruct 511 []] else []))
  end).

Fixpoint word_length_source {A} (values : list A) : domain_run nat := word_mark (
  match values with
  | [] => (0%nat, [])
  | _ :: rest => count <- word_length_source rest ;; domain_return 512 [] (S count)
  end).

Definition word_popcount w x : domain_run Z :=
  let count := Pos.to_nat w in
  let '(indices, sequence_trace) := word_sequence_source count 0 in
  let '(selected, filter_trace) := word_pop_filter w x indices in
  let '(result, length_trace) := word_length_source selected in
  (Z.of_nat result, AuditArithmetic 513 [N.pos w] :: sequence_trace ++ filter_trace ++
    length_trace ++ [AuditArithmetic 505 [N.of_nat result]]).

Definition word_unary_source o w x : domain_run Z := word_mark (
  match o with
  | bvnot => domain_wnot w x
  | bvneg => word_neg w x
  | bvclz => word_clz w x
  | bvctz => kb_wctz w x
  | bvpopcnt => word_popcount w x
  | _ => (0%Z, [])
  end).

Definition word_binary_source o w x y : domain_run Z := word_mark (
  match o with
  | bvadd => raw <- domain_z DzAdd x y ;; domain_wrap w raw
  | bvsub => raw <- domain_z DzSub x y ;; domain_wrap w raw
  | bvmul => raw <- domain_z DzMul x y ;; domain_wrap w raw
  | bvudiv => word_udiv false w x y
  | bvurem => word_udiv true w x y
  | bvsdiv => word_signed_div false w x y
  | bvsrem => word_signed_div true w x y
  | bvsmod => word_smod w x y
  | bvand => domain_word_bits DzAnd w x y
  | bvor => domain_word_bits DzOr w x y
  | bvxor => domain_word_bits DzXor w x y
  | bvshl | bvlshr | bvashr | bvrotl | bvrotr => kb_word_shift o w x y
  | _ => (0%Z, [])
  end).

Definition word_compare_source o w x y : domain_run bool := word_mark (
  match o with
  | bveq | bvne =>
    first <- domain_wrap w x ;;
    second <- domain_wrap w y ;;
    same <- domain_equal first second ;;
    domain_return 514 [] (match o with bveq => same | _ => negb same end)
  | bvult | bvule =>
    first <- domain_wrap w x ;;
    second <- domain_wrap w y ;;
    domain_compare (match o with bvult => true | _ => false end) first second
  | bvslt | bvsle =>
    first <- kb_signed w x ;;
    second <- kb_signed w y ;;
    domain_compare (match o with bvslt => true | _ => false end) first second
  | _ => (false, [])
  end).

(** Width checking explicitly prices unary index conversions and both strict ite width tests. *)
Definition word_width_source o (widths : list width) : domain_run (option width) := word_mark (
  let output := result_width o widths in
  let events := match o, widths with
    | bvite, [c; a; b] =>
      [AuditArithmetic 504 [N.pos c; 1%N]; AuditArithmetic 504 [N.pos a; N.pos b]]
    | bvconcat, [a; b] | bvzext b, [a] | bvsext b, [a] =>
      [AuditArithmetic 504 [N.pos a; N.pos b]]
    | bvtrunc target, [source] => [AuditArithmetic 504 [N.pos target; N.pos source]]
    | bvextract hi lo, [w] =>
      [AuditArithmetic 515 [N.of_nat lo; N.of_nat hi; N.pos w]] ++
      (if Nat.leb lo hi && Nat.ltb hi (Pos.to_nat w)
       then [AuditArithmetic 516 [N.of_nat hi; N.of_nat lo]] else [])
    | _, [a; b] => [AuditArithmetic 504 [N.pos a; N.pos b]]
    | _, _ => []
    end in
  (output, events)).

Fixpoint word_normalize_source (values : list word) : domain_run (list word) := word_mark (
  match values with
  | [] => ([], [])
  | (w, z) :: rest =>
    normalized <- domain_wrap w z ;;
    later <- word_normalize_source rest ;;
    domain_return 517 [] ((w, normalized) :: later)
  end).

Definition word_value_source o (values : list word) : domain_run Z := word_mark (
  match o, values with
  | bvite, [(_, condition); (_, x); (_, y)] =>
    yes <- domain_equal condition 1 ;; domain_return 518 [] (if yes then x else y)
  | bvzext _, [(_, x)] | bvtrunc _, [(_, x)] => (x, [])
  | bvsext _, [(w, x)] => kb_signed w x
  | bvextract _ lo, [(_, x)] =>
    let amount := Z.of_nat lo in
    let '(out, body) := power <- domain_z DzPow 2 amount ;; domain_z DzDiv x power in
    (out, AuditArithmetic 505 [N.of_nat lo] :: body)
  | bvconcat, [(_, x); (w, y)] =>
    m <- domain_modulus w ;;
    product <- domain_z DzMul x m ;; domain_z DzAdd product y
  | _, [(w, x)] =>
    match word_fun1 o with Some _ => word_unary_source o w x | None => (0%Z, []) end
  | _, [(w, x); (_, y)] =>
    match word_fun2 o, word_cmp o with
    | Some _, _ => word_binary_source o w x y
    | _, Some _ => test <- word_compare_source o w x y ;;
      domain_return 518 [] (if test then 1 else 0)
    | _, _ => (0%Z, [])
    end
  | _, _ => (0%Z, [])
  end).

Definition word_eval_source o (values : list word) : domain_run (option word) := word_mark (
  target <- word_width_source o (map fst values) ;;
  match target with
  | None => domain_return 519 [] None
  | Some rw =>
    normalized <- word_normalize_source values ;;
    raw <- word_value_source o normalized ;;
    out <- domain_wrap rw raw ;; domain_return 519 [] (Some (rw, out))
  end).

Definition word_frame_weight (event : audit_event unit) : nat :=
  match event with
  | AuditCase 510 _ => 100%nat
  | AuditArithmetic 513 [width] => S (N.to_nat width)
  | AuditArithmetic 515 [lo; hi; w] =>
    (100 + N.to_nat w + Nat.min (N.to_nat lo) (N.to_nat hi) +
      Nat.min (N.to_nat hi) (N.to_nat w))%nat
  | AuditArithmetic 516 [hi; lo] => (100 + N.to_nat hi + N.to_nat lo)%nat
  | _ => kb_frame_weight event
  end.

Definition word_source_work (events : audit_trace unit) : nat :=
  fold_right (fun event total => (word_frame_weight event + total)%nat) 0%nat events.

(** The complete primitive source model preserves every eval_op outcome and normalized word. *)
Definition word_eval_source_erases_type : Prop := forall o values,
  fst (word_eval_source o values) = eval_op o values.
```

## Galois.Domains.DomainsAuditTransferWrapped

Card: AUD-DT-WRAPPED

Source destination: `theories/Domains/DomainsAuditTransferWrapped.v`.

```rocq
(** * Complete wrapped forward source equations
    Four-way and signed/unsigned products retain every repeated call.
    Builds on: IntervalWhole and ProductWhole. *)
From Stdlib Require Import List NArith ZArith Bool.
From Galois.Bits Require Import BitsWord BitsFun BitsOp.
From Galois.Domains Require Import DomainsInterval DomainsWrapped.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Domains Require Import DomainsAuditNumericCost.
From Galois.Domains Require Import DomainsAuditKnownBitsSource.
From Galois.Domains Require Import DomainsAuditTransferWord.
From Galois.Domains Require Import DomainsAuditTransferInterval.
From Galois.Domains Require Import DomainsAuditProductSource.
Import ListNotations.
Definition wr_mark {A} (r : domain_run A) := domain_case 530 [] r.
Definition wr_size w a := wr_mark (match a with WBot => (0%Z,[]) | WFull => domain_modulus w
 | WItv lo hi => offset <- product_offset_source w lo hi ;; domain_z DzAdd offset 1 end).
Definition wr_cover w a b c := first <- product_wrapped_order_source w a c ;;
 second <- product_wrapped_order_source w b c ;; domain_return 531 [] (first && second).
Definition wr_choose w a b first second := yes <- wr_cover w a b first ;;
 if yes then another <- wr_cover w a b second ;; if another then
 fs <- wr_size w first ;; ss <- wr_size w second ;; smaller <- domain_compare false fs ss ;;
 (if smaller then first else second,[]) else (first,[]) else
 another <- wr_cover w a b second ;; (if another then second else WFull,[]).
Definition wr_join w a b := wr_mark (ab <- product_wrapped_order_source w a b ;;
 chosen <- (if ab then (b,[]) else ba <- product_wrapped_order_source w b a ;;
 if ba then (a,[]) else match a,b with WItv lo hi,WItv lo' hi' =>
 first <- domain_return 532 [] (WItv lo hi') ;; second <- domain_return 532 [] (WItv lo' hi) ;;
 wr_choose w a b first second | _,_ => (WFull,[]) end) ;; product_wrapped_norm_source w chosen).
Definition wr_four w a b c d := first <- wr_join w a b ;; second <- wr_join w c d ;; wr_join w
  first second.
Definition wr_range w lo hi := wr_mark (empty <- domain_compare true hi lo ;; if empty then
  (WBot,[]) else
 m <- domain_modulus w ;; upper <- domain_z DzSub m 1 ;; distance <- domain_z DzSub hi lo ;;
 full <- domain_compare false upper distance ;; if full then (WFull,[]) else
   product_wrapped_norm_source w (WItv lo hi)).
Definition wr_of_interval w a := wr_mark (match a with IBot => (WBot,[]) | Itv(Fin lo)(Fin hi) =>
  wr_range w lo hi | _ => (WFull,[]) end).
Definition wr_parts_raw w a := wr_mark (match a with WBot => ((IBot,IBot),[]) | WFull => top <-
  iv_top w ;; ((top,IBot),[])
 | WItv lo hi => low <- domain_wrap w lo ;; high <- domain_wrap w hi ;;
 ordered <- domain_compare false low high ;; if ordered then first <- iv_make low high ;;
   ((first,IBot),[]) else
 m <- domain_modulus w ;; upper <- domain_z DzSub m 1 ;; first <- iv_make low upper ;; second <-
   iv_make 0 high ;;
 domain_return 533 [] (first,second) end).
Definition wr_parts w a := normalized <- product_wrapped_norm_source w a ;; wr_parts_raw w
  normalized.
Definition wr_add w a b := wr_mark (match a,b with WBot,_ | _,WBot => (WBot,[])
 | WItv lo hi,WItv lo' hi' => m <- domain_modulus w ;; sa <- wr_size w a ;; sb <- wr_size w b ;;
 sum <- domain_z DzAdd sa sb ;; full <- domain_compare true m sum ;; if full then (WFull,[]) else
 low <- domain_z DzAdd lo lo' ;; high <- domain_z DzAdd hi hi' ;; product_wrapped_norm_source w
   (WItv low high)
 | _,_ => (WFull,[]) end).
Definition wr_neg w a := wr_mark (match a with WItv lo hi => low <- domain_z DzSub 0 hi ;;
 high <- domain_z DzSub 0 lo ;; product_wrapped_norm_source w (WItv low high) | _ => (a,[]) end).
Definition wr_sub w a b := negative <- wr_neg w b ;; wr_add w a negative.
Definition wr_products (maximum : bool) lo hi lo' hi' :=
 a <- domain_z DzMul lo lo' ;; b <- domain_z DzMul lo hi' ;;
 first <- domain_z (if maximum then DzMax else DzMin) a b ;;
 c <- domain_z DzMul hi lo' ;; d <- domain_z DzMul hi hi' ;;
 second <- domain_z (if maximum then DzMax else DzMin) c d ;;
 domain_z (if maximum then DzMax else DzMin) first second.
Definition wr_mul_piece w a b := wr_mark (match a,b with IBot,_ | _,IBot => (WBot,[])
 | Itv(Fin lo)(Fin hi),Itv(Fin lo')(Fin hi') =>
 low <- wr_products false lo hi lo' hi' ;; high <- wr_products true lo hi lo' hi' ;; wr_range w low
   high
 | _,_ => (WFull,[]) end).
Definition wr_shift_bound delta b := match b with Fin z => out <- domain_z DzAdd z delta ;;
  domain_return 534 [] (Fin out) | _ => (b,[]) end.
Definition wr_shift_interval delta a := match a with IBot => (IBot,[]) | Itv lo hi =>
 low <- wr_shift_bound delta lo ;; high <- wr_shift_bound delta hi ;; domain_return 535 [] (Itv low
   high) end.
Definition wr_signed_parts w a := h1 <- kb_half w ;; h2 <- kb_half w ;;
 bias <- domain_return 536 [] (WItv h1 h2) ;; biased <- wr_add w a bias ;; pieces <- wr_parts w
   biased ;;
 h3 <- kb_half w ;; d1 <- domain_z DzSub 0 h3 ;; first <- wr_shift_interval d1 (fst pieces) ;;
 h4 <- kb_half w ;; d2 <- domain_z DzSub 0 h4 ;; second <- wr_shift_interval d2 (snd pieces) ;;
 domain_return 537 [] (first,second).
Definition wr_mul_parts w (a b : interval*interval) :=
 first <- wr_mul_piece w (fst a)(fst b) ;; second <- wr_mul_piece w (fst a)(snd b) ;;
 third <- wr_mul_piece w (snd a)(fst b) ;; fourth <- wr_mul_piece w (snd a)(snd b) ;; wr_four w
   first second third fourth.
Definition wr_mul_cut pole a := previous <- domain_z DzSub pole 1 ;;
 first <- iv_meet a (Itv NegInf (Fin previous)) ;; second <- iv_meet a (Itv (Fin pole) PosInf) ;;
 domain_return 538 [] (first,second).
Definition wr_mul_both w pole (a b : interval*interval) :=
 a0 <- wr_mul_cut pole (fst a) ;; a1 <- wr_mul_cut pole (snd a) ;;
 b0 <- wr_mul_cut pole (fst b) ;; b1 <- wr_mul_cut pole (snd b) ;;
 first <- wr_mul_parts w a0 b0 ;; second <- wr_mul_parts w a0 b1 ;;
 third <- wr_mul_parts w a1 b0 ;; fourth <- wr_mul_parts w a1 b1 ;; wr_four w first second third
   fourth.
Definition wr_mul w a b := wr_mark (
 h <- kb_half w ;; pa <- wr_parts w a ;; pb <- wr_parts w b ;; unsigned <- wr_mul_both w h pa pb ;;
 sa <- wr_signed_parts w a ;; sb <- wr_signed_parts w b ;; signed <- wr_mul_both w 0 sa sb ;;
 us <- wr_size w unsigned ;; ss <- wr_size w signed ;; smaller <- domain_compare false us ss ;;
 domain_return 539 [] (if smaller then unsigned else signed)).
Definition wr_signed_piece (division : bool) w a b := wr_mark (match a,b with IBot,_ | _,IBot =>
  (WBot,[]) | _,_ =>
 sa <- iv_sign w a ;; match sa with
 | Some xa => sb <- iv_sign w b ;; match sb with
 | Some xb =>
 aa <- (if xa then iv_neg w a else (a,[])) ;; bb <- (if xb then iv_neg w b else (b,[])) ;;
 value <- (if division then iv_udiv w aa bb else iv_urem w aa bb) ;; magnitude <- wr_of_interval w
   value ;;
 if (if division then xorb xa xb else xa) then wr_neg w magnitude else (magnitude,[])
 | _ => (WFull,[]) end
 | _ => (WFull,[]) end end).
Definition wr_project target source q := pieces <- wr_parts source q ;;
 first <- wr_of_interval target (fst pieces) ;; second <- wr_of_interval target (snd pieces) ;;
   wr_join target first second.
Definition wr_pole_cut w a := h1 <- kb_half w ;; previous <- domain_z DzSub h1 1 ;;
 first <- iv_meet a (Itv(Fin 0)(Fin previous)) ;; h2 <- kb_half w ;;
 m <- domain_modulus w ;; upper <- domain_z DzSub m 1 ;;
 second <- iv_meet a (Itv(Fin h2)(Fin upper)) ;; domain_return 540 [] (first,second).
Definition wr_piece o args rw := out <- iv_forward o args rw ;; wr_of_interval rw out.
Definition wr_unary o w a rw := pieces <- wr_parts w a ;;
 first <- wr_piece o [(w,fst pieces)] rw ;; second <- wr_piece o [(w,snd pieces)] rw ;; wr_join rw
   first second.
Definition wr_piece_binary o wa wb a b rw := match o with
 | bvsdiv => wr_signed_piece true rw a b | bvsrem => wr_signed_piece false rw a b
 | _ => wr_piece o [(wa,a);(wb,b)] rw end.
Definition wr_piece_cut o wa wb a b rw := pa <- wr_pole_cut wa a ;; pb <- wr_pole_cut wb b ;;
 first <- wr_piece_binary o wa wb (fst pa)(fst pb) rw ;; second <- wr_piece_binary o wa wb (fst
   pa)(snd pb) rw ;;
 third <- wr_piece_binary o wa wb (snd pa)(fst pb) rw ;; fourth <- wr_piece_binary o wa wb (snd
   pa)(snd pb) rw ;;
 wr_four rw first second third fourth.
Definition wr_binary o wa wb a b rw := pa <- wr_parts wa a ;; pb <- wr_parts wb b ;;
 first <- wr_piece_cut o wa wb (fst pa)(fst pb) rw ;; second <- wr_piece_cut o wa wb (fst pa)(snd
   pb) rw ;;
 third <- wr_piece_cut o wa wb (snd pa)(fst pb) rw ;; fourth <- wr_piece_cut o wa wb (snd pa)(snd
   pb) rw ;;
 wr_four rw first second third fourth.
Definition wr_forward o (args : list(width*wrapped)) rw := wr_mark (match o,args with
 | bvneg,[(_,a)] => wr_neg rw a | (bvzext _|bvtrunc _),[(w,a)] => wr_project rw w a
 | bvadd,[(_,a);(_,b)] => wr_add rw a b | bvsub,[(_,a);(_,b)] => wr_sub rw a b
 | bvmul,[(_,a);(_,b)] => wr_mul rw a b | bvite,[_;(_,a);(_,b)] => wr_join rw a b
 | _,[(w,a)] => wr_unary o w a rw | _,[(wa,a);(wb,b)] => wr_binary o wa wb a b rw | _,_ =>
   (WFull,[]) end).
Definition wr_frame_weight event := match event with AuditCase 530 _ => 100%nat | _ =>
  iv_frame_weight event end.
Definition wr_work trace := fold_right (fun e n => (wr_frame_weight e+n)%nat) 0%nat trace.
Definition wr_forward_erases_type : Prop := forall o args rw, fst(wr_forward o args
  rw)=wrapped_forward o args rw.
Definition wr_helpers_erases_type : Prop :=
 (forall w a b, fst(wr_mul w a b)=wrapped_mul w a b) /\
 (forall w a, fst(wr_parts w a)=wrapped_parts w a) /\
 (forall w a b, fst(wr_join w a b)=wrapped_join w a b).
```

## Galois.Domains.DomainsAuditWiden

Card: AUD-DW

Source destination: `theories/Domains/DomainsAuditWiden.v`.

```rocq
(** * Widening statement check

    This scratch file elaborates the selected widening and its obligations.
    For example, its rank is measured after reduction.
    Builds on: DomainsSignedBounds and OrderLattice. *)

From Stdlib Require Import ZArith NArith Bool.
From Galois.Bits Require Import BitsWord.
From Galois.Order Require Import OrderLattice.
From Galois.Domains Require Import DomainsNumeric DomainsKnownBits DomainsSignedBounds
  DomainsSignedBoundsDomain.

(** * Candidate definitions and proposition types *)

Definition audit_half_top (w : width) (s : bool) : sb_half :=
  sb_reduce_half w s (SBRange tnum_top 0 (modulus w - 1)).

Definition audit_half_widen (w : width) (s : bool) (a b : sb_half) : sb_half :=
  if sb_leb w s b a then sb_reduce_half w s a else audit_half_top w s.

Definition audit_widen (w : width) (a b : signed_bounds) : signed_bounds :=
  SignedBounds (audit_half_widen w false (sb_zero a) (sb_zero b))
    (audit_half_widen w true (sb_one a) (sb_one b)).

Definition audit_widen_lattice (w : width) : lattice signed_bounds :=
  {| leb := leb (signed_bounds_lattice w);
     bot := bot (signed_bounds_lattice w);
     join := join (signed_bounds_lattice w);
     widen := audit_widen w;
     narrow := narrow (signed_bounds_lattice w) |}.

Definition audit_widen_measure (w : width) (a : signed_bounds) : nat :=
  (if sb_leb w false (audit_half_top w false) (sb_zero a) then 0 else 1) +
  (if sb_leb w true (audit_half_top w true) (sb_one a) then 0 else 1).

Definition audit_widen_domain : word_domain signed_bounds :=
  {| plat := audit_widen_lattice;
     ptop := ptop signed_bounds_domain;
     pconst := pconst signed_bounds_domain;
     pforward := pforward signed_bounds_domain;
     passume := passume signed_bounds_domain;
     pmeet := pmeet signed_bounds_domain |}.

Definition audit_widen_encloses_type : Prop := forall w a b,
  leb (signed_bounds_lattice w) a (audit_widen w a b) = true /\
  leb (signed_bounds_lattice w) b (audit_widen w a b) = true.

Definition audit_widen_post_reduction_rank_type : Prop := forall w a b,
  leb (signed_bounds_lattice w) b a = false ->
  (audit_widen_measure w (audit_widen w a b) < audit_widen_measure w a)%nat.

Definition audit_widen_bounded_type : Prop := forall w a,
  (audit_widen_measure w a <= 2)%nat.

Definition audit_widen_sound_type : Prop := forall w a b z,
  (signed_bounds_gamma w a z \/ signed_bounds_gamma w b z) ->
  signed_bounds_gamma w (audit_widen w a b) z.
Definition audit_widen_laws_type : Prop := forall w, lattice_laws (audit_widen_lattice w).
Definition audit_widen_domain_laws_type : Prop := word_laws audit_widen_domain signed_bounds_gamma.

(** Fixed measure stability is a library proof obligation. *)
Definition audit_widen_rank_stable_type : Prop := forall w a b,
  leb (audit_widen_lattice w) b a = true ->
  (audit_widen_measure w (audit_widen w a b) <= audit_widen_measure w a)%nat.

(** A rank witness must expose the fixed computational measure and bound. *)
Definition audit_widen_rank_exists_type : Prop := forall w,
  exists r : bounded_widening_rank (audit_widen_lattice w),
    (forall a, wrank (base_wrank r) a = audit_widen_measure w a) /\ wbound r = 2%nat.

(** This constructor uses only erased proofs of its fixed library obligations. *)
Definition audit_widen_rank_builder (stable : audit_widen_rank_stable_type)
    (progress : audit_widen_post_reduction_rank_type) (bounded : audit_widen_bounded_type)
    (w : width) : bounded_widening_rank (audit_widen_lattice w) :=
  BoundedWideningRank signed_bounds (audit_widen_lattice w)
    (WideningRank signed_bounds (audit_widen_lattice w) (audit_widen_measure w)
      (stable w) (progress w)) 2 (bounded w).

(** Every evidence instantiation exposes exactly the fixed measure and constant bound. *)
Definition audit_widen_rank_builder_measure_type : Prop := forall stable progress bounded w a,
  let r := audit_widen_rank_builder stable progress bounded w in
  wrank (base_wrank r) a = audit_widen_measure w a /\ wbound r = 2%nat.
```

## Galois.Domains.DomainsAuditWidenSource

Card: AUD-DW

Source destination: `theories/Domains/DomainsAuditWidenSource.v`.

```rocq
(** * Complete signed-half widening source equations

    Every reduction, strict order operand and boundary search child is composed here.
    For example, an excluded half pays old, new and returned-half reduction.
    Builds on: DomainPrimitive and DomainsSignedBoundsDomain. *)

From Stdlib Require Import List NArith PArith ZArith Bool.
From Galois.Order Require Import OrderLattice.
From Galois.Bits Require Import BitsWord.
From Galois.Domains Require Import DomainsKnownBits DomainsSignedBounds
  DomainsSignedBoundsDomain.
From Galois.Domains Require Import DomainsAuditWiden.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Domains Require Import DomainsAuditNumericCost.
Import List.ListNotations.

Definition widen_range (t : tnum) (lo hi : Z) : domain_run sb_half :=
  domain_return 230 [count_zencode lo; count_zencode hi] (SBRange t lo hi).

Definition widen_merge (w : width) (a b : sb_half) : domain_run sb_half :=
  domain_case 231 []
    (match a, b with
    | SBEmpty, _ => (b, [])
    | _, SBEmpty => (a, [])
    | SBRange ta la ua, SBRange tb lb ub =>
      bits <- domain_tnum_bits DzAnd w ta tb ;;
      lo <- domain_z DzMin la lb ;;
      hi <- domain_z DzMax ua ub ;; widen_range bits lo hi
    end).

Definition widen_bit (index : Z) (value : bool) : domain_run tnum :=
  domain_case 232 [if value then 1%N else 0%N]
    (if value then power <- domain_z DzPow 2 index ;; domain_tnum 0 power
     else power <- domain_z DzPow 2 index ;; domain_tnum power 0).

Definition widen_fix (w : width) (t : tnum) (index : Z) (value : bool)
    : domain_run tnum :=
  bit <- widen_bit index value ;; domain_tnum_bits DzOr w t bit.

(** All four endpoint computations occur strictly in the two Boolean guards. *)
Fixpoint widen_search (fuel : positive) (w : width) (t : tnum) (lo hi : Z)
    : domain_run sb_half :=
  domain_case 233 [N.pos fuel]
    (empty <- domain_empty w t ;;
    domain_case 234 [if empty then 1%N else 0%N]
      (if empty then domain_return 235 [] SBEmpty else
       upper <- domain_max w t ;;
       below <- domain_compare true upper lo ;;
       lower <- domain_min w t ;;
       above <- domain_compare true hi lower ;;
       let outside := below || above in
       domain_case 236 [if below then 1%N else 0%N; if above then 1%N else 0%N]
         (domain_case 237 [if outside then 1%N else 0%N]
           (if outside then domain_return 235 [] SBEmpty else
            lower2 <- domain_min w t ;;
            low_inside <- domain_compare false lo lower2 ;;
            upper2 <- domain_max w t ;;
            high_inside <- domain_compare false upper2 hi ;;
            let inside := low_inside && high_inside in
            domain_case 238 [if low_inside then 1%N else 0%N;
              if high_inside then 1%N else 0%N]
              (domain_case 239 [if inside then 1%N else 0%N]
                (if inside then
                   norm <- domain_normalise w t ;;
                   lower3 <- domain_min w t ;;
                   upper3 <- domain_max w t ;; widen_range norm lower3 upper3
                 else
                   match fuel with
                   | xH => domain_return 235 [] SBEmpty
                   | xO rest | xI rest =>
                     let index := Z.log2 (Z.pos rest) in
                     let log_trace := [AuditArithmetic 240 [count_zencode (Z.pos rest)]] in
                     let '(lhs_t, lhs_fix) := widen_fix w t index false in
                     let '(lhs, first) := widen_search rest w lhs_t lo hi in
                     let '(rhs_t, rhs_fix) := widen_fix w t index true in
                     let '(rhs, second) := widen_search rest w rhs_t lo hi in
                     let '(out, merged) := widen_merge w lhs rhs in
                     (out, log_trace ++ lhs_fix ++ first ++ rhs_fix ++ second ++ merged)
                   end)))))).

(** Reduction includes both clipping operands, repeated modulus construction and the bit fix. *)
Definition widen_reduce (w : width) (sign : bool) (half : sb_half) : domain_run sb_half :=
  domain_case 241 []
    (match half with
    | SBEmpty => domain_return 235 [] SBEmpty
    | SBRange t lo hi =>
      clipped_lo <- domain_z DzMax 0 lo ;;
      m <- domain_modulus w ;;
      upper <- domain_z DzSub m 1 ;;
      clipped_hi <- domain_z DzMin upper hi ;;
      empty <- domain_compare true clipped_hi clipped_lo ;;
      domain_case 242 [if empty then 1%N else 0%N]
        (if empty then domain_return 235 [] SBEmpty else
          marker <- domain_modulus w ;;
          let fuel := Z.to_pos marker in
          index <- domain_z DzSub (Z.pos w) 1 ;;
          fixed <- widen_fix w t index sign ;;
          let '(out, body) := widen_search fuel w fixed clipped_lo clipped_hi in
          (out, AuditArithmetic 243 [count_zencode marker] :: body))
    end).

(** Half order computes all strict Boolean operands even after the first false result. *)
Definition widen_order (w : width) (a b : sb_half) : domain_run bool :=
  domain_case 244 []
    (match a, b with
    | SBEmpty, _ => (true, [])
    | _, SBEmpty => (false, [])
    | SBRange ta la ua, SBRange tb lb ub =>
      bits <- domain_order w ta tb ;;
      low <- domain_compare false lb la ;;
      high <- domain_compare false ua ub ;;
      (bits && low && high, [AuditCase 245 []; AuditCase 245 []])
    end).

Definition widen_leb (w : width) (sign : bool) (a b : sb_half) : domain_run bool :=
  lhs <- widen_reduce w sign a ;;
  rhs <- widen_reduce w sign b ;; widen_order w lhs rhs.

Definition widen_top (w : width) (sign : bool) : domain_run sb_half :=
  m <- domain_modulus w ;;
  upper <- domain_z DzSub m 1 ;;
  ignored <- domain_tell [AuditConstruct 218 [0%N; 0%N]] ;;
  raw <- widen_range tnum_top 0 upper ;; widen_reduce w sign raw.

Definition widen_half_source (w : width) (sign : bool) (a b : sb_half)
    : domain_run sb_half :=
  included <- widen_leb w sign b a ;;
  domain_case 246 [if included then 1%N else 0%N]
    (if included then widen_reduce w sign a else widen_top w sign).

(** Both sign halves and the returned reduced representation belong to this execution. *)
Definition audit_widen_source (w : width) (a b : signed_bounds)
    : domain_run signed_bounds :=
  let '(z, first) := widen_half_source w false (sb_zero a) (sb_zero b) in
  let '(o, second) := widen_half_source w true (sb_one a) (sb_one b) in
  (SignedBounds z o, [AuditCase 247 []; AuditCase 247 []] ++ first ++
    [AuditCase 248 []; AuditCase 248 []] ++ second ++ [AuditConstruct 249 []]).

(** Rank measures include the two actual top constructions and four nested reductions. *)
Definition audit_widen_measure_source (w : width) (a : signed_bounds) : domain_run nat :=
  ztop <- widen_top w false ;;
  z <- widen_leb w false ztop (sb_zero a) ;;
  otop <- widen_top w true ;;
  o <- widen_leb w true otop (sb_one a) ;;
  (((if z then 0 else 1) + (if o then 0 else 1))%nat,
    [AuditCase 247 []; AuditCase 248 []; AuditCase 250 [if z then 1%N else 0%N];
      AuditCase 250 [if o then 1%N else 0%N];
      AuditArithmetic 2 [if z then 0%N else 1%N; if o then 0%N else 1%N]]).

Definition widen_frame_weight (event : audit_event unit) : nat :=
  match event with
  | AuditArithmetic 240 [z] | AuditArithmetic 243 [z] =>
    audit_unary_conversion_weight (audit_z_bits (count_zdecode z))
  | _ => domain_frame_weight event
  end.

Definition widen_work (events : audit_trace unit) : nat :=
  fold_right (fun event total => (widen_frame_weight event + total)%nat) 0%nat events.

Definition widen_half_size (half : sb_half) : nat :=
  match half with
  | SBEmpty => 1
  | SBRange t lo hi =>
    (1 + audit_z_bits (zeros t) + audit_z_bits (ones t) +
      audit_z_bits lo + audit_z_bits hi)%nat
  end.

Definition widen_input_size w (a b : signed_bounds) : nat :=
  (1 + Pos.to_nat w + widen_half_size (sb_zero a) + widen_half_size (sb_one a) +
    widen_half_size (sb_zero b) + widen_half_size (sb_one b))%nat.

(** The result erases to the separately selectable widening's fixed half equations. *)
Definition audit_widen_source_erases_type : Prop := forall w a b,
  fst (audit_widen_source w a b) =
    SignedBounds
      (if sb_leb w false (sb_zero b) (sb_zero a)
       then sb_reduce_half w false (sb_zero a)
       else sb_reduce_half w false (SBRange tnum_top 0 (modulus w - 1)))
      (if sb_leb w true (sb_one b) (sb_one a)
       then sb_reduce_half w true (sb_one a)
       else sb_reduce_half w true (SBRange tnum_top 0 (modulus w - 1))).

(** The initialized clipped search has at most the two boundary paths and stopping siblings. *)
Definition widen_reduce_nodes_type : Prop := forall w sign half,
  (audit_case_count 233 (snd (widen_reduce w sign half)) <= 1 + 4 * Pos.to_nat w)%nat.

(** The complete widening cost includes six reductions, two orders and the final construction. *)
Definition audit_widen_source_bound_type : Prop := forall w a b,
  let size := widen_input_size w a b in
  (widen_work (snd (audit_widen_source w a b)) <=
    1000000 * (Pos.to_nat w + 1) * (size + 1) * (size + 1))%nat.

(** The separate actual rank computation has the same raw-input polynomial envelope. *)
Definition audit_widen_measure_source_bound_type : Prop := forall w a,
  let size := widen_input_size w a a in
  (widen_work (snd (audit_widen_measure_source w a)) <=
    1000000 * (Pos.to_nat w + 1) * (size + 1) * (size + 1))%nat.

(** The widening observer preserves the concrete public widening body. *)
Definition audit_widen_plain_erases_type : Prop := forall w a b,
  fst (audit_widen_source w a b) = audit_widen w a b.
```

### `DomainsAuditTransfer.audit_div_one_fallback`

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransfer.v`.

```rocq
Theorem audit_div_one_fallback :
forall (o : BitsOp.op) (wps : list (BitsWord.width * DomainsSignedBounds.signed_bounds))
  (rw : BitsWord.width),
audit_div_one_guard o wps rw = false ->
audit_div_one_forward o wps rw =
@DomainsNumeric.pforward DomainsSignedBounds.signed_bounds
  DomainsSignedBoundsDomain.signed_bounds_domain o wps rw.
```

### `DomainsAuditTransfer.audit_div_one_laws`

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransfer.v`.

```rocq
Theorem audit_div_one_laws :
@DomainsNumeric.word_laws DomainsSignedBounds.signed_bounds audit_div_one_domain
  DomainsSignedBounds.signed_bounds_gamma.
```

### `DomainsAuditTransfer.audit_div_one_refines`

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransfer.v`.

```rocq
Theorem audit_div_one_refines :
forall (o : BitsOp.op) (wps : list (BitsWord.width * DomainsSignedBounds.signed_bounds))
  (rw : BitsWord.width),
@OrderLattice.leb DomainsSignedBounds.signed_bounds
  (DomainsSignedBoundsDomain.signed_bounds_lattice rw) (audit_div_one_forward o wps rw)
  (@DomainsNumeric.pforward DomainsSignedBounds.signed_bounds
     DomainsSignedBoundsDomain.signed_bounds_domain o wps rw) =
true.
```

### `DomainsAuditTransfer.audit_div_one_strict`

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransfer.v`.

```rocq
Theorem audit_div_one_strict :
let input :=
  (4%positive, audit_dividend)
  :: (4%positive, audit_divisor) :: @nil (positive * DomainsSignedBounds.signed_bounds) in
@OrderLattice.leb DomainsSignedBounds.signed_bounds
  (DomainsSignedBoundsDomain.signed_bounds_lattice 4%positive)
  (DomainsSignedBoundsDomain.signed_bounds_const 4%positive 1) audit_existing_division =
true /\
@OrderLattice.leb DomainsSignedBounds.signed_bounds
  (DomainsSignedBoundsDomain.signed_bounds_lattice 4%positive)
  (DomainsSignedBoundsDomain.signed_bounds_const 4%positive 1)
  (audit_div_one_forward BitsOp.bvsdiv input 4%positive) =
false.
```

### `DomainsAuditMul.audit_mul_active_bits_bound`

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMul.v`.

```rocq
Theorem audit_mul_active_bits_bound :
forall (w : BitsWord.width) (b : DomainsKnownBits.tnum),
(audit_mul_active_bits w b <= N.pos w)%N.
```

### `DomainsAuditMul.audit_mul_bottom`

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMul.v`.

```rocq
Theorem audit_mul_bottom :
forall (w : BitsWord.width) (a b : DomainsKnownBits.tnum),
DomainsKnownBits.tnum_empty w a || DomainsKnownBits.tnum_empty w b = true ->
DomainsAuditMulPlain.audit_mul w a b =
@OrderLattice.bot DomainsKnownBits.tnum (DomainsKnownBits.tnum_lattice w).
```

### `DomainsAuditMul.audit_mul_constants`

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMul.v`.

```rocq
Theorem audit_mul_constants :
forall (w : BitsWord.width) (x y : Z),
DomainsAuditMulPlain.audit_mul w
  (@DomainsNumeric.pconst DomainsKnownBits.tnum DomainsKnownBits.known_bits_domain w x)
  (@DomainsNumeric.pconst DomainsKnownBits.tnum DomainsKnownBits.known_bits_domain w y) =
@DomainsNumeric.pconst DomainsKnownBits.tnum DomainsKnownBits.known_bits_domain w
  (BitsFun.wmul w x y).
```

### `DomainsAuditMul.audit_mul_counted_bounds`

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMul.v`.

```rocq
Theorem audit_mul_counted_bounds :
forall (w : BitsWord.width) (a b : DomainsKnownBits.tnum),
let
'(_, work) := DomainsAuditMulPlain.audit_mul_counted w a b in
 let active := audit_mul_active_bits w b in
 (DomainsAuditMulPlain.audit_mul_steps work <= active)%N /\
 (DomainsAuditMulPlain.audit_mul_tests work <= 2 * active)%N /\
 (DomainsAuditMulPlain.audit_mul_additions work <= N.succ active)%N /\
 (DomainsAuditMulPlain.audit_mul_shifts work <= active)%N /\
 (DomainsAuditMulPlain.audit_mul_products work <= 1)%N.
```

### `DomainsAuditMulSource.audit_mul_counted_plain_erases`

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMulSource.v`.

```rocq
Theorem audit_mul_counted_plain_erases :
forall (w : BitsWord.width) (a b : DomainsKnownBits.tnum),
let
'(result, work, _) := audit_mul_counted_source w a b in
 DomainsAuditMulPlain.audit_mul_counted w a b =
 (result,
  {|
    DomainsAuditMulPlain.audit_mul_steps := mul_steps work;
    DomainsAuditMulPlain.audit_mul_tests := mul_tests work;
    DomainsAuditMulPlain.audit_mul_additions := mul_adds work;
    DomainsAuditMulPlain.audit_mul_shifts := mul_shifts work;
    DomainsAuditMulPlain.audit_mul_products := mul_products work
  |}).
```

### `DomainsAuditMul.audit_mul_meet_bottom`

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMul.v`.

```rocq
Theorem audit_mul_meet_bottom :
forall (w : BitsWord.width) (a b : DomainsKnownBits.tnum),
DomainsKnownBits.tnum_empty w a || DomainsKnownBits.tnum_empty w b = true ->
DomainsAuditMulPlain.audit_mul_meet w a b =
@OrderLattice.bot DomainsKnownBits.tnum (DomainsKnownBits.tnum_lattice w).
```

### `DomainsAuditMul.audit_mul_meet_constants`

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMul.v`.

```rocq
Theorem audit_mul_meet_constants :
forall (w : BitsWord.width) (x y : Z),
DomainsAuditMulPlain.audit_mul_meet w
  (@DomainsNumeric.pconst DomainsKnownBits.tnum DomainsKnownBits.known_bits_domain w x)
  (@DomainsNumeric.pconst DomainsKnownBits.tnum DomainsKnownBits.known_bits_domain w y) =
@DomainsNumeric.pconst DomainsKnownBits.tnum DomainsKnownBits.known_bits_domain w
  (BitsFun.wmul w x y).
```

### `DomainsAuditMul.audit_mul_meet_intersection`

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMul.v`.

```rocq
Theorem audit_mul_meet_intersection :
forall (w : BitsWord.width) (a b : DomainsKnownBits.tnum) (z : Z),
DomainsKnownBits.tnum_gamma w (DomainsAuditMulPlain.audit_mul_meet w a b) z <->
DomainsKnownBits.tnum_gamma w (DomainsAuditMulPlain.audit_mul w a b) z /\
DomainsKnownBits.tnum_gamma w (DomainsKnownBitsFast.tnum_mul_precise w a b) z.
```

### `DomainsAuditMulSource.audit_mul_meet_plain_erases`

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMulSource.v`.

```rocq
Theorem audit_mul_meet_plain_erases :
forall (w : BitsWord.width) (a b : DomainsKnownBits.tnum),
@fst DomainsKnownBits.tnum (CollectionsAuditCost.audit_trace unit)
  (audit_mul_meet_source w a b) =
DomainsAuditMulPlain.audit_mul_meet w a b.
```

### `DomainsAuditMul.audit_mul_meet_sound`

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMul.v`.

```rocq
Theorem audit_mul_meet_sound :
forall (w : BitsWord.width) (a b : DomainsKnownBits.tnum) (x y : Z),
BitsWord.is_word w x ->
BitsWord.is_word w y ->
DomainsKnownBits.tnum_gamma w a x ->
DomainsKnownBits.tnum_gamma w b y ->
DomainsKnownBits.tnum_gamma w (DomainsAuditMulPlain.audit_mul_meet w a b) (BitsFun.wmul w x y).
```

### `DomainsAuditMul.audit_mul_meet_width`

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMul.v`.

```rocq
Theorem audit_mul_meet_width :
forall (w : BitsWord.width) (a b : DomainsKnownBits.tnum),
DomainsKnownBits.tnum_normalise w (DomainsAuditMulPlain.audit_mul_meet w a b) =
DomainsAuditMulPlain.audit_mul_meet w a b.
```

### `DomainsAuditMul.audit_mul_meet_word_laws`

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMul.v`.

```rocq
Theorem audit_mul_meet_word_laws :
@DomainsNumeric.word_laws DomainsKnownBits.tnum DomainsAuditMulPlain.audit_mul_meet_domain
  DomainsKnownBits.tnum_gamma.
```

### `DomainsAuditMul.audit_mul_sound`

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMul.v`.

```rocq
Theorem audit_mul_sound :
forall (w : BitsWord.width) (a b : DomainsKnownBits.tnum) (x y : Z),
BitsWord.is_word w x ->
BitsWord.is_word w y ->
DomainsKnownBits.tnum_gamma w a x ->
DomainsKnownBits.tnum_gamma w b y ->
DomainsKnownBits.tnum_gamma w (DomainsAuditMulPlain.audit_mul w a b) (BitsFun.wmul w x y).
```

### `DomainsAuditMulSource.audit_mul_source_bound`

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMulSource.v`.

```rocq
Theorem audit_mul_source_bound :
forall (w : positive) (a b : DomainsKnownBits.tnum),
let size := mul_input_size w a b in
let budget :=
  Init.Nat.of_num_uint
    (Number.UIntDecimal
       (Decimal.D1
          (Decimal.D0
             (Decimal.D0
                (Decimal.D0 (Decimal.D0 (Decimal.D0 (Decimal.D0 (Decimal.D0 Decimal.Nil))))))))) *
  (Pos.to_nat w + 1) * (size + 1) * (size + 1) in
domain_work
  (@snd (DomainsKnownBits.tnum * mul_stats) (CollectionsAuditCost.audit_trace unit)
     (audit_mul_counted_source w a b)) <=
budget /\
domain_work
  (@snd DomainsKnownBits.tnum (CollectionsAuditCost.audit_trace unit) (mul_dom8_source w a b)) <=
budget /\
domain_work
  (@snd DomainsKnownBits.tnum (CollectionsAuditCost.audit_trace unit)
     (audit_mul_meet_source w a b)) <=
3 * budget.
```

### `DomainsAuditMulSource.audit_mul_source_counts`

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMulSource.v`.

```rocq
Theorem audit_mul_source_counts :
forall (w : BitsWord.width) (a b : DomainsKnownBits.tnum),
let
'(_, stats, _) := audit_mul_counted_source w a b in
 let active :=
   N.size
     (Z.to_N (BitsFun.wor w (DomainsKnownBits.tnum_min w b) (DomainsKnownBits.tnum_mask w b)))
   in
 (mul_steps stats <= active)%N /\
 (mul_tests stats <= 2 * active)%N /\
 (mul_adds stats <= active + 1)%N /\
 (mul_shifts stats <= active)%N /\ (mul_products stats <= 1)%N.
```

### `DomainsAuditMul.audit_mul_steps_exact`

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMul.v`.

```rocq
Theorem audit_mul_steps_exact :
forall (w : BitsWord.width) (a b : DomainsKnownBits.tnum),
DomainsKnownBits.tnum_empty w a || DomainsKnownBits.tnum_empty w b = false ->
DomainsAuditMulPlain.audit_mul_steps
  (@snd DomainsKnownBits.tnum DomainsAuditMulPlain.audit_mul_work
     (DomainsAuditMulPlain.audit_mul_counted w a b)) =
audit_mul_active_bits w b.
```

### `DomainsAuditMul.audit_mul_width`

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMul.v`.

```rocq
Theorem audit_mul_width :
forall (w : BitsWord.width) (a b : DomainsKnownBits.tnum),
DomainsKnownBits.tnum_normalise w (DomainsAuditMulPlain.audit_mul w a b) =
DomainsAuditMulPlain.audit_mul w a b.
```

### `DomainsAuditMul.audit_mul_word_laws`

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMul.v`.

```rocq
Theorem audit_mul_word_laws :
@DomainsNumeric.word_laws DomainsKnownBits.tnum DomainsAuditMulPlain.audit_mul_domain
  DomainsKnownBits.tnum_gamma.
```

### `DomainsAuditReduceBits.audit_reduce_bits_plain_erases`

Card: AUD-DR

Source destination: `theories/Domains/DomainsAuditReduceBits.v`.

```rocq
Theorem audit_reduce_bits_plain_erases :
forall (w : BitsWord.width) (input : DomainsKnownBits.tnum * DomainsWrapped.wrapped),
@fst (DomainsKnownBits.tnum * DomainsWrapped.wrapped)
  (CollectionsAuditCost.audit_trace (reduce_call DomainsKnownBits.tnum DomainsWrapped.wrapped))
  (audit_reduce_bits_source w input) =
audit_reduce_bits w input.
```

### `DomainsAuditReduceBits.audit_reduce_bits_source_bound`

Card: AUD-DR

Source destination: `theories/Domains/DomainsAuditReduceBits.v`.

```rocq
Theorem audit_reduce_bits_source_bound :
forall (w : positive) (a : DomainsKnownBits.tnum) (b : DomainsWrapped.wrapped),
let raw :=
  match b with
  | DomainsWrapped.WItv lo hi =>
      CollectionsAuditCost.audit_z_bits lo + CollectionsAuditCost.audit_z_bits hi
  | _ => 1
  end in
let size :=
  1 + Pos.to_nat w + CollectionsAuditCost.audit_z_bits (DomainsKnownBits.zeros a) +
  CollectionsAuditCost.audit_z_bits (DomainsKnownBits.ones a) + raw in
reduce_bits_whole_work
  (@snd (DomainsKnownBits.tnum * DomainsWrapped.wrapped)
     (CollectionsAuditCost.audit_trace
        (reduce_call DomainsKnownBits.tnum DomainsWrapped.wrapped))
     (audit_reduce_bits_source w (a, b))) <=
Init.Nat.of_num_uint
  (Number.UIntDecimal
     (Decimal.D1
        (Decimal.D0
           (Decimal.D0
              (Decimal.D0
                 (Decimal.D0
      (Decimal.D0 (Decimal.D0 (Decimal.D0 (Decimal.D0 (Decimal.D0
        Decimal.Nil))))))))))) *
(Pos.to_nat w + 1) * (Pos.to_nat w + 1) * (size + 1) * (size + 1) *
(size + 1) * (size + 1).
```

### `DomainsAuditReduceBits.audit_reduce_bits_source_erases`

Card: AUD-DR

Source destination: `theories/Domains/DomainsAuditReduceBits.v`.

```rocq
Theorem audit_reduce_bits_source_erases :
forall (w : BitsWord.width) (input : DomainsKnownBits.tnum * DomainsWrapped.wrapped),
@fst (DomainsKnownBits.tnum * DomainsWrapped.wrapped)
  (CollectionsAuditCost.audit_trace (reduce_call DomainsKnownBits.tnum DomainsWrapped.wrapped))
  (audit_reduce_bits_source w input) =
@reduce_loop_reference DomainsKnownBits.tnum DomainsWrapped.wrapped
  DomainsKnownBits.known_bits_domain DomainsWrapped.wrapped_domain reduce_bits_exchange w
  (N.succ_pos (reduce_bits_rank w input)) input.
```

### `DomainsAuditReduce.audit_reduce_gamma`

Card: AUD-DR

Source destination: `theories/Domains/DomainsAuditReduce.v`.

```rocq
Theorem audit_reduce_gamma :
forall (P Q : Type) (D1 : DomainsNumeric.word_domain P) (D2 : DomainsNumeric.word_domain Q)
  (G1 : BitsWord.width -> P -> Z -> Prop) (G2 : BitsWord.width -> Q -> Z -> Prop)
  (exchange : audit_exchange P Q),
@audit_exchange_laws P Q D1 D2 G1 G2 exchange ->
forall (w : BitsWord.width) (x : P * Q) (z : Z),
@DomainsProduct.product_pgamma P Q G1 G2 w (@audit_reduce P Q D1 D2 exchange w x) z <->
@DomainsProduct.product_pgamma P Q G1 G2 w x z.
```

### `DomainsAuditReduce.audit_reduce_rank`

Card: AUD-DR

Source destination: `theories/Domains/DomainsAuditReduce.v`.

```rocq
Theorem audit_reduce_rank :
forall (P Q : Type) (D1 : DomainsNumeric.word_domain P) (D2 : DomainsNumeric.word_domain Q)
  (G1 : BitsWord.width -> P -> Z -> Prop) (G2 : BitsWord.width -> Q -> Z -> Prop)
  (exchange : audit_exchange P Q),
@audit_exchange_laws P Q D1 D2 G1 G2 exchange ->
forall (w : BitsWord.width) (x : P * Q),
@OrderLattice.leb (P * Q)
  (@OrderProduct.product_lattice P Q (@DomainsNumeric.plat P D1 w)
     (@DomainsNumeric.plat Q D2 w))
  x (@audit_exchange_step P Q exchange w x) =
false ->
(@audit_exchange_rank P Q exchange w (@audit_exchange_step P Q exchange w x) <
 @audit_exchange_rank P Q exchange w x)%N.
```

### `DomainsAuditReduceSource.audit_reduce_source_bound`

Card: AUD-DR

Source destination: `theories/Domains/DomainsAuditReduceSource.v`.

```rocq
Theorem audit_reduce_source_bound :
forall (P Q : Type) (D1 : DomainsNumeric.word_domain P) (D2 : DomainsNumeric.word_domain Q)
  (exchange : audit_exchange P Q) (w : BitsWord.width) (input : P * Q)
  (body_work : reduce_call P Q -> nat),
let
'(_, events) := @audit_reduce_source P Q D1 D2 exchange w input in
 let rank := @audit_exchange_rank P Q exchange w input in
 @reduce_library_work P Q events + @reduce_client_body_work P Q body_work events <=
 50 * N.to_nat (N.succ rank) + 2 * CollectionsAuditCost.audit_z_bits (Z.of_N rank) +
 @reduce_client_body_work P Q body_work events.
```

### `DomainsAuditReduceSource.audit_reduce_source_calls`

Card: AUD-DR

Source destination: `theories/Domains/DomainsAuditReduceSource.v`.

```rocq
Theorem audit_reduce_source_calls :
forall (P Q : Type) (D1 : DomainsNumeric.word_domain P) (D2 : DomainsNumeric.word_domain Q)
  (exchange : audit_exchange P Q) (w : BitsWord.width) (input : P * Q),
let
'(_, events) := @audit_reduce_source P Q D1 D2 exchange w input in
 @reduce_step_calls P Q events <=
 3 * N.to_nat (N.succ (@audit_exchange_rank P Q exchange w input)) /\
 @CollectionsAuditCost.audit_work (reduce_call P Q) events <=
 40 * N.to_nat (N.succ (@audit_exchange_rank P Q exchange w input)) + 2.
```

### `DomainsAuditReduceSource.audit_reduce_source_erases`

Card: AUD-DR

Source destination: `theories/Domains/DomainsAuditReduceSource.v`.

```rocq
Theorem audit_reduce_source_erases :
forall (P Q : Type) (D1 : DomainsNumeric.word_domain P) (D2 : DomainsNumeric.word_domain Q)
  (exchange : audit_exchange P Q) (w : BitsWord.width) (input : P * Q),
@fst (P * Q) (CollectionsAuditCost.audit_trace (reduce_call P Q))
  (@audit_reduce_source P Q D1 D2 exchange w input) =
@reduce_loop_reference P Q D1 D2 exchange w
  (N.succ_pos (@audit_exchange_rank P Q exchange w input)) input.
```

### `DomainsAuditReduce.audit_reduce_stable`

Card: AUD-DR

Source destination: `theories/Domains/DomainsAuditReduce.v`.

```rocq
Theorem audit_reduce_stable :
forall (P Q : Type) (D1 : DomainsNumeric.word_domain P) (D2 : DomainsNumeric.word_domain Q)
  (G1 : BitsWord.width -> P -> Z -> Prop) (G2 : BitsWord.width -> Q -> Z -> Prop)
  (exchange : audit_exchange P Q),
@audit_exchange_laws P Q D1 D2 G1 G2 exchange ->
forall (w : BitsWord.width) (x : P * Q),
let y := @audit_reduce P Q D1 D2 exchange w x in
@OrderLattice.leb (P * Q)
  (@OrderProduct.product_lattice P Q (@DomainsNumeric.plat P D1 w)
     (@DomainsNumeric.plat Q D2 w))
  y (@audit_exchange_step P Q exchange w y) =
true.
```

### `DomainsAuditReduce.audit_reduce_word_laws`

Card: AUD-DR

Source destination: `theories/Domains/DomainsAuditReduce.v`.

```rocq
Theorem audit_reduce_word_laws :
forall (P Q : Type) (D1 : DomainsNumeric.word_domain P) (D2 : DomainsNumeric.word_domain Q)
  (G1 : BitsWord.width -> P -> Z -> Prop) (G2 : BitsWord.width -> Q -> Z -> Prop)
  (exchange : audit_exchange P Q),
@DomainsNumeric.word_laws P D1 G1 ->
@DomainsNumeric.word_laws Q D2 G2 ->
@audit_exchange_laws P Q D1 D2 G1 G2 exchange ->
@DomainsNumeric.word_laws (P * Q)
  (@DomainsProduct.product_word_domain P Q D1 D2 (@audit_reduce P Q D1 D2 exchange))
  (@DomainsProduct.product_pgamma P Q G1 G2).
```

### `DomainsAuditTransfer.audit_transfer_shapes`

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransfer.v`.

```rocq
Theorem audit_transfer_shapes :
(forall (o : BitsOp.op) (wps : list (BitsWord.width * DomainsSignedBounds.signed_bounds))
   (rw : BitsWord.width),
 audit_div_one_guard o wps rw = false ->
 audit_div_one_forward o wps rw =
 @DomainsNumeric.pforward DomainsSignedBounds.signed_bounds
   DomainsSignedBoundsDomain.signed_bounds_domain o wps rw) /\
(forall (o : BitsOp.op) (args : list (BitsWord.width * DomainsSignedBounds.signed_bounds))
   (rw : BitsWord.width),
 (forall a b : DomainsSignedBounds.signed_bounds,
  o = BitsOp.bvsdiv ->
  args = (rw, a) :: (rw, b) :: @nil (BitsWord.width * DomainsSignedBounds.signed_bounds) ->
  False) ->
 audit_div_one_forward o args rw =
 @DomainsNumeric.pforward DomainsSignedBounds.signed_bounds
   DomainsSignedBoundsDomain.signed_bounds_domain o args rw) /\
(forall a b : DomainsSignedBounds.signed_bounds,
 audit_div_one_forward BitsOp.bvsdiv
   ((1%positive, a) :: (1%positive, b) :: @nil (positive * DomainsSignedBounds.signed_bounds))
   1%positive =
 @DomainsNumeric.pforward DomainsSignedBounds.signed_bounds
   DomainsSignedBoundsDomain.signed_bounds_domain BitsOp.bvsdiv
   ((1%positive, a) :: (1%positive, b) :: @nil (positive * DomainsSignedBounds.signed_bounds))
   1%positive) /\
(forall (w : BitsWord.width) (a : DomainsSignedBounds.signed_bounds),
 audit_div_one_forward BitsOp.bvsdiv
   ((w, a)
    :: (w, DomainsSignedBoundsDomain.signed_bounds_const w 0)
       :: @nil (BitsWord.width * DomainsSignedBounds.signed_bounds))
   w =
 @DomainsNumeric.pforward DomainsSignedBounds.signed_bounds
   DomainsSignedBoundsDomain.signed_bounds_domain BitsOp.bvsdiv
   ((w, a)
    :: (w, DomainsSignedBoundsDomain.signed_bounds_const w 0)
       :: @nil (BitsWord.width * DomainsSignedBounds.signed_bounds))
   w) /\
(forall (o : BitsOp.op) (args : list (BitsWord.width * DomainsSignedBounds.signed_bounds))
   (rw : BitsWord.width),
 o <> BitsOp.bvsdiv ->
 audit_div_one_forward o args rw =
 @DomainsNumeric.pforward DomainsSignedBounds.signed_bounds
   DomainsSignedBoundsDomain.signed_bounds_domain o args rw) /\
(forall (w : BitsWord.width) (t : DomainsKnownBits.tnum) (z : Z),
 BitsWord.is_word w z ->
 DomainsKnownBits.tnum_gamma w t z ->
 DomainsSignedBounds.signed_bounds_gamma w
   (DomainsSignedBoundsDomain.sb_from_components w t DomainsWrapped.WFull) z).
```

### `DomainsAuditTransfer.audit_transfer_sound`

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransfer.v`.

```rocq
Theorem audit_transfer_sound :
forall (o : BitsOp.op) (wps : list (BitsWord.width * DomainsSignedBounds.signed_bounds))
  (ys : list BitsWord.word) (rw : BitsWord.width) (z : Z),
@Forall2 (BitsWord.width * DomainsSignedBounds.signed_bounds) BitsWord.word
  (@DomainsNumeric.payload_sound DomainsSignedBounds.signed_bounds
     DomainsSignedBounds.signed_bounds_gamma)
  wps ys ->
BitsOp.eval_op o ys = @Some (BitsWord.width * Z) (rw, z) ->
DomainsSignedBounds.signed_bounds_gamma rw (audit_div_one_forward o wps rw) z.
```

### `DomainsAuditWiden.audit_widen_bounded`

Card: AUD-DW

Source destination: `theories/Domains/DomainsAuditWiden.v`.

```rocq
Theorem audit_widen_bounded :
forall (w : BitsWord.width) (a : DomainsSignedBounds.signed_bounds),
audit_widen_measure w a <= 2.
```

### `DomainsAuditWiden.audit_widen_domain_laws`

Card: AUD-DW

Source destination: `theories/Domains/DomainsAuditWiden.v`.

```rocq
Theorem audit_widen_domain_laws :
@DomainsNumeric.word_laws DomainsSignedBounds.signed_bounds audit_widen_domain
  DomainsSignedBounds.signed_bounds_gamma.
```

### `DomainsAuditWiden.audit_widen_encloses`

Card: AUD-DW

Source destination: `theories/Domains/DomainsAuditWiden.v`.

```rocq
Theorem audit_widen_encloses :
forall (w : BitsWord.width) (a b : DomainsSignedBounds.signed_bounds),
@OrderLattice.leb DomainsSignedBounds.signed_bounds
  (DomainsSignedBoundsDomain.signed_bounds_lattice w) a (audit_widen w a b) =
true /\
@OrderLattice.leb DomainsSignedBounds.signed_bounds
  (DomainsSignedBoundsDomain.signed_bounds_lattice w) b (audit_widen w a b) =
true.
```

### `DomainsAuditWiden.audit_widen_laws`

Card: AUD-DW

Source destination: `theories/Domains/DomainsAuditWiden.v`.

```rocq
Theorem audit_widen_laws :
forall w : BitsWord.width,
@OrderLattice.lattice_laws DomainsSignedBounds.signed_bounds (audit_widen_lattice w).
```

### `DomainsAuditWidenSource.audit_widen_measure_source_bound`

Card: AUD-DW

Source destination: `theories/Domains/DomainsAuditWidenSource.v`.

```rocq
Theorem audit_widen_measure_source_bound :
forall (w : positive) (a : DomainsSignedBounds.signed_bounds),
let size := widen_input_size w a a in
widen_work (@snd nat (CollectionsAuditCost.audit_trace unit) (audit_widen_measure_source w a)) <=
Init.Nat.of_num_uint
  (Number.UIntDecimal
     (Decimal.D1
        (Decimal.D0
           (Decimal.D0 (Decimal.D0 (Decimal.D0 (Decimal.D0 (Decimal.D0 Decimal.Nil)))))))) *
(Pos.to_nat w + 1) * (size + 1) * (size + 1).
```

### `DomainsAuditWidenSource.audit_widen_plain_erases`

Card: AUD-DW

Source destination: `theories/Domains/DomainsAuditWidenSource.v`.

```rocq
Theorem audit_widen_plain_erases :
forall (w : BitsWord.width) (a b : DomainsSignedBounds.signed_bounds),
@fst DomainsSignedBounds.signed_bounds (CollectionsAuditCost.audit_trace unit)
  (audit_widen_source w a b) =
audit_widen w a b.
```

### `DomainsAuditWiden.audit_widen_post_reduction_rank`

Card: AUD-DW

Source destination: `theories/Domains/DomainsAuditWiden.v`.

```rocq
Theorem audit_widen_post_reduction_rank :
forall (w : BitsWord.width) (a b : DomainsSignedBounds.signed_bounds),
@OrderLattice.leb DomainsSignedBounds.signed_bounds
  (DomainsSignedBoundsDomain.signed_bounds_lattice w) b a =
false -> audit_widen_measure w (audit_widen w a b) < audit_widen_measure w a.
```

### `DomainsAuditWiden.audit_widen_rank_builder_measure`

Card: AUD-DW

Source destination: `theories/Domains/DomainsAuditWiden.v`.

```rocq
Theorem audit_widen_rank_builder_measure :
forall (stable : audit_widen_rank_stable_type)
  (progress : audit_widen_post_reduction_rank_type) (bounded : audit_widen_bounded_type)
  (w : BitsWord.width) (a : DomainsSignedBounds.signed_bounds),
let r := audit_widen_rank_builder stable progress bounded w in
@OrderLattice.wrank DomainsSignedBounds.signed_bounds (audit_widen_lattice w)
  (@OrderLattice.base_wrank DomainsSignedBounds.signed_bounds (audit_widen_lattice w) r) a =
audit_widen_measure w a /\
@OrderLattice.wbound DomainsSignedBounds.signed_bounds (audit_widen_lattice w) r = 2.
```

### `DomainsAuditWiden.audit_widen_rank_exists`

Card: AUD-DW

Source destination: `theories/Domains/DomainsAuditWiden.v`.

```rocq
Theorem audit_widen_rank_exists :
forall w : BitsWord.width,
exists
  r : @OrderLattice.bounded_widening_rank DomainsSignedBounds.signed_bounds
        (audit_widen_lattice w),
  (forall a : DomainsSignedBounds.signed_bounds,
   @OrderLattice.wrank DomainsSignedBounds.signed_bounds (audit_widen_lattice w)
     (@OrderLattice.base_wrank DomainsSignedBounds.signed_bounds (audit_widen_lattice w) r) a =
   audit_widen_measure w a) /\
  @OrderLattice.wbound DomainsSignedBounds.signed_bounds (audit_widen_lattice w) r = 2.
```

### `DomainsAuditWiden.audit_widen_rank_stable`

Card: AUD-DW

Source destination: `theories/Domains/DomainsAuditWiden.v`.

```rocq
Theorem audit_widen_rank_stable :
forall (w : BitsWord.width) (a b : DomainsSignedBounds.signed_bounds),
@OrderLattice.leb DomainsSignedBounds.signed_bounds (audit_widen_lattice w) b a = true ->
audit_widen_measure w (audit_widen w a b) <= audit_widen_measure w a.
```

### `DomainsAuditWiden.audit_widen_sound`

Card: AUD-DW

Source destination: `theories/Domains/DomainsAuditWiden.v`.

```rocq
Theorem audit_widen_sound :
forall (w : BitsWord.width) (a b : DomainsSignedBounds.signed_bounds) (z : Z),
DomainsSignedBounds.signed_bounds_gamma w a z \/ DomainsSignedBounds.signed_bounds_gamma w b z ->
DomainsSignedBounds.signed_bounds_gamma w (audit_widen w a b) z.
```

### `DomainsAuditWidenSource.audit_widen_source_bound`

Card: AUD-DW

Source destination: `theories/Domains/DomainsAuditWidenSource.v`.

```rocq
Theorem audit_widen_source_bound :
forall (w : positive) (a b : DomainsSignedBounds.signed_bounds),
let size := widen_input_size w a b in
widen_work
  (@snd DomainsSignedBounds.signed_bounds (CollectionsAuditCost.audit_trace unit)
     (audit_widen_source w a b)) <=
Init.Nat.of_num_uint
  (Number.UIntDecimal
     (Decimal.D1
        (Decimal.D0
           (Decimal.D0 (Decimal.D0 (Decimal.D0 (Decimal.D0 (Decimal.D0 Decimal.Nil)))))))) *
(Pos.to_nat w + 1) * (size + 1) * (size + 1).
```

### `DomainsAuditWidenSource.audit_widen_source_erases`

Card: AUD-DW

Source destination: `theories/Domains/DomainsAuditWidenSource.v`.

```rocq
Theorem audit_widen_source_erases :
forall (w : BitsWord.width) (a b : DomainsSignedBounds.signed_bounds),
@fst DomainsSignedBounds.signed_bounds (CollectionsAuditCost.audit_trace unit)
  (audit_widen_source w a b) =
{|
  DomainsSignedBounds.sb_zero :=
    if
     DomainsSignedBoundsDomain.sb_leb w false (DomainsSignedBounds.sb_zero b)
       (DomainsSignedBounds.sb_zero a)
    then DomainsSignedBounds.sb_reduce_half w false (DomainsSignedBounds.sb_zero a)
    else
     DomainsSignedBounds.sb_reduce_half w false
       (DomainsSignedBounds.SBRange DomainsKnownBits.tnum_top 0 (BitsWord.modulus w - 1));
  DomainsSignedBounds.sb_one :=
    if
     DomainsSignedBoundsDomain.sb_leb w true (DomainsSignedBounds.sb_one b)
       (DomainsSignedBounds.sb_one a)
    then DomainsSignedBounds.sb_reduce_half w true (DomainsSignedBounds.sb_one a)
    else
     DomainsSignedBounds.sb_reduce_half w true
       (DomainsSignedBounds.SBRange DomainsKnownBits.tnum_top 0 (BitsWord.modulus w - 1))
|}.
```

### `DomainsAuditNumericAdequacy.domain_helpers_erases`

Card: AUD-DOM-ADEQUACY

Source destination: `theories/Domains/DomainsAuditNumericAdequacy.v`.

```rocq
Theorem domain_helpers_erases :
(forall (w : BitsWord.width) (a : DomainsKnownBits.tnum),
 @fst bool (CollectionsAuditCost.audit_trace unit) (domain_empty w a) =
 DomainsKnownBits.tnum_empty w a) /\
(forall (w : BitsWord.width) (a b : DomainsKnownBits.tnum) (initial : bool),
 @fst DomainsKnownBits.tnum (CollectionsAuditCost.audit_trace unit) (domain_adc w a b initial) =
 DomainsKnownBits.tnum_adc w a b initial) /\
(forall (w : BitsWord.width) (amount : Z) (a : DomainsKnownBits.tnum),
 @fst DomainsKnownBits.tnum (CollectionsAuditCost.audit_trace unit) (domain_shift w amount a) =
 DomainsKnownBits.tnum_scalar BitsOp.bvshl w amount a) /\
(forall (w : BitsWord.width) (a b : DomainsKnownBits.tnum),
 @fst bool (CollectionsAuditCost.audit_trace unit) (domain_order w a b) =
 @OrderLattice.leb DomainsKnownBits.tnum (DomainsKnownBits.tnum_lattice w) a b).
```

### `DomainsAuditNumericAdequacy.domain_helpers_full_erases`

Card: AUD-DOM-ADEQUACY

Source destination: `theories/Domains/DomainsAuditNumericAdequacy.v`.

```rocq
Theorem domain_helpers_full_erases :
(forall w : BitsWord.width,
 @fst Z (CollectionsAuditCost.audit_trace unit) (domain_modulus w) = BitsWord.modulus w) /\
(forall (w : BitsWord.width) (z : Z),
 @fst Z (CollectionsAuditCost.audit_trace unit) (domain_wrap w z) = BitsWord.wrap w z) /\
(forall (w : BitsWord.width) (z : Z),
 @fst Z (CollectionsAuditCost.audit_trace unit) (domain_wnot w z) = BitsFun.wnot w z) /\
(forall (w : BitsWord.width) (z : Z),
 @fst DomainsKnownBits.tnum (CollectionsAuditCost.audit_trace unit) (domain_const w z) =
 DomainsKnownBits.tnum_const w z) /\
(forall (w : BitsWord.width) (a : DomainsKnownBits.tnum),
 @fst DomainsKnownBits.tnum (CollectionsAuditCost.audit_trace unit) (domain_normalise w a) =
 DomainsKnownBits.tnum_normalise w a) /\
(forall (w : BitsWord.width) (a : DomainsKnownBits.tnum),
 @fst Z (CollectionsAuditCost.audit_trace unit) (domain_min w a) =
 DomainsKnownBits.tnum_min w a) /\
(forall (w : BitsWord.width) (a : DomainsKnownBits.tnum),
 @fst Z (CollectionsAuditCost.audit_trace unit) (domain_max w a) =
 DomainsKnownBits.tnum_max w a) /\
(forall (w : BitsWord.width) (a : DomainsKnownBits.tnum),
 @fst Z (CollectionsAuditCost.audit_trace unit) (domain_mask w a) =
 DomainsKnownBits.tnum_mask w a) /\
(forall w : BitsWord.width,
 @fst DomainsKnownBits.tnum (CollectionsAuditCost.audit_trace unit) (domain_bottom w) =
 @OrderLattice.bot DomainsKnownBits.tnum (DomainsKnownBits.tnum_lattice w)) /\
(forall (w : BitsWord.width) (a b : DomainsKnownBits.tnum),
 @fst DomainsKnownBits.tnum (CollectionsAuditCost.audit_trace unit)
   (domain_tnum_bits DzAnd w a b) =
 DomainsKnownBits.tnum_join w a b) /\
(forall (w : BitsWord.width) (a b : DomainsKnownBits.tnum),
 @fst DomainsKnownBits.tnum (CollectionsAuditCost.audit_trace unit)
   (domain_tnum_bits DzOr w a b) =
 DomainsKnownBits.tnum_meet w a b) /\
domain_helpers_erases_type.
```

### `DomainsAuditTransferInterval.iv_forward_erases`

Card: AUD-DT-INTERVAL

Source destination: `theories/Domains/DomainsAuditTransferInterval.v`.

```rocq
Theorem iv_forward_erases :
forall (o : BitsOp.op) (args : list (BitsWord.width * DomainsInterval.interval))
  (rw : BitsWord.width),
@fst DomainsInterval.interval (CollectionsAuditCost.audit_trace unit) (iv_forward o args rw) =
DomainsInterval.interval_forward o args rw.
```

### `DomainsAuditTransferBounds.iv_forward_source_bound`

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransferBounds.v`.

```rocq
Theorem iv_forward_source_bound :
forall (o : BitsOp.op) (args : list (BitsWord.width * DomainsInterval.interval))
  (rw : BitsWord.width),
iv_work
  (@snd DomainsInterval.interval (CollectionsAuditCost.audit_trace unit) (iv_forward o args rw)) <=
numeric_envelope (numeric_iv_dimension o args rw).
```

### `DomainsAuditTransferInterval.iv_helpers_erases`

Card: AUD-DT-INTERVAL

Source destination: `theories/Domains/DomainsAuditTransferInterval.v`.

```rocq
Theorem iv_helpers_erases :
(forall (w : BitsWord.width) (a b : DomainsInterval.interval),
 @fst DomainsInterval.interval (CollectionsAuditCost.audit_trace unit) (iv_add_mod w a b) =
 DomainsInterval.interval_add_modular w a b) /\
(forall (w : BitsWord.width) (a b : DomainsInterval.interval),
 @fst DomainsInterval.interval (CollectionsAuditCost.audit_trace unit) (iv_smod w a b) =
 DomainsInterval.interval_smod w a b) /\
(forall (w : BitsWord.width) (a b : DomainsInterval.interval),
 @fst DomainsInterval.interval (CollectionsAuditCost.audit_trace unit) (iv_ashr w a b) =
 DomainsInterval.interval_ashr w a b).
```

### `DomainsAuditTransferBounds.iv_source_total`

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransferBounds.v`.

```rocq
Theorem iv_source_total :
forall (o : BitsOp.op) (args : list (BitsWord.width * DomainsInterval.interval))
  (rw : BitsWord.width),
exists (r : DomainsInterval.interval) (t : CollectionsAuditCost.audit_trace unit),
  iv_forward o args rw = (r, t).
```

### `DomainsAuditTransferBounds.iv_source_unique`

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransferBounds.v`.

```rocq
Theorem iv_source_unique :
forall (o : BitsOp.op) (args : list (BitsWord.width * DomainsInterval.interval))
  (rw : BitsWord.width) (r1 : DomainsInterval.interval)
  (t1 : CollectionsAuditCost.audit_trace unit) (r2 : DomainsInterval.interval)
  (t2 : CollectionsAuditCost.audit_trace unit),
iv_forward o args rw = (r1, t1) -> iv_forward o args rw = (r2, t2) -> r1 = r2 /\ t1 = t2.
```

### `DomainsAuditNumericAdequacy.kb_classic_mul_source_bound`

Card: AUD-DOM-ADEQUACY

Source destination: `theories/Domains/DomainsAuditNumericAdequacy.v`.

```rocq
Theorem kb_classic_mul_source_bound :
forall (w : BitsWord.width) (a b : DomainsKnownBits.tnum),
kb_source_work
  (@snd DomainsKnownBits.tnum (CollectionsAuditCost.audit_trace unit) (kb_classic_mul w a b)) <=
numeric_envelope
  (numeric_kb_dimension BitsOp.bvmul
     ((w, a) :: (w, b) :: @nil (BitsWord.width * DomainsKnownBits.tnum)) w).
```

### `DomainsAuditNumericAdequacy.kb_empty_scan_source_count`

Card: AUD-DOM-ADEQUACY

Source destination: `theories/Domains/DomainsAuditNumericAdequacy.v`.

```rocq
Theorem kb_empty_scan_source_count :
forall args : list (BitsWord.width * DomainsKnownBits.tnum),
@length (BitsWord.width * DomainsKnownBits.tnum) args <=
@CollectionsAuditCost.audit_case_count unit 500
  (@snd bool (CollectionsAuditCost.audit_trace unit) (kb_any_empty_source args)).
```

### `DomainsAuditNumericAdequacy.kb_forward_source_bound`

Card: AUD-DOM-ADEQUACY

Source destination: `theories/Domains/DomainsAuditNumericAdequacy.v`.

```rocq
Theorem kb_forward_source_bound :
forall (o : BitsOp.op) (args : list (BitsWord.width * DomainsKnownBits.tnum))
  (rw : BitsWord.width),
kb_source_work
  (@snd DomainsKnownBits.tnum (CollectionsAuditCost.audit_trace unit)
     (kb_forward_source o args rw)) <=
numeric_envelope (numeric_kb_dimension o args rw).
```

### `DomainsAuditNumericAdequacy.kb_forward_source_erases`

Card: AUD-DOM-ADEQUACY

Source destination: `theories/Domains/DomainsAuditNumericAdequacy.v`.

```rocq
Theorem kb_forward_source_erases :
forall (o : BitsOp.op) (args : list (BitsWord.width * DomainsKnownBits.tnum))
  (rw : BitsWord.width),
@fst DomainsKnownBits.tnum (CollectionsAuditCost.audit_trace unit)
  (kb_forward_source o args rw) =
DomainsKnownBits.tnum_forward o args rw.
```

### `DomainsAuditNumericAdequacy.kb_source_total`

Card: AUD-DOM-ADEQUACY

Source destination: `theories/Domains/DomainsAuditNumericAdequacy.v`.

```rocq
Theorem kb_source_total :
forall (o : BitsOp.op) (args : list (BitsWord.width * DomainsKnownBits.tnum))
  (rw : BitsWord.width),
exists (r : DomainsKnownBits.tnum) (t : CollectionsAuditCost.audit_trace unit),
  kb_forward_source o args rw = (r, t).
```

### `DomainsAuditNumericAdequacy.kb_source_unique`

Card: AUD-DOM-ADEQUACY

Source destination: `theories/Domains/DomainsAuditNumericAdequacy.v`.

```rocq
Theorem kb_source_unique :
forall (o : BitsOp.op) (args : list (BitsWord.width * DomainsKnownBits.tnum))
  (rw : BitsWord.width) (r1 : DomainsKnownBits.tnum)
  (t1 : CollectionsAuditCost.audit_trace unit) (r2 : DomainsKnownBits.tnum)
  (t2 : CollectionsAuditCost.audit_trace unit),
kb_forward_source o args rw = (r1, t1) ->
kb_forward_source o args rw = (r2, t2) -> r1 = r2 /\ t1 = t2.
```

### `DomainsAuditMulDispatch.mul_dispatch_fallback`

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMulDispatch.v`.

```rocq
Theorem mul_dispatch_fallback :
forall (meet : bool) (o : BitsOp.op) (args : list (positive * DomainsKnownBits.tnum))
  (rw : positive),
match o with
| BitsOp.bvmul =>
    fun args0 : list (positive * DomainsKnownBits.tnum) =>
    match args0 with
    | @nil _ => false
    | (wa, _) :: @nil _ => false
    | (wa, _) :: (wb, _) :: @nil _ => (wa =? rw)%positive && (wb =? rw)%positive
    | (wa, _) :: (wb, _) :: _ :: _ => false
    end
| _ => fun _ : list (positive * DomainsKnownBits.tnum) => false
end args = false ->
@fst DomainsKnownBits.tnum (CollectionsAuditCost.audit_trace unit)
  (mul_dispatch_source meet o args rw) =
DomainsKnownBits.tnum_forward o args rw.
```

### `DomainsAuditMulDispatch.mul_dispatch_source_bound`

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMulDispatch.v`.

```rocq
Theorem mul_dispatch_source_bound :
forall (meet : bool) (o : BitsOp.op) (args : list (BitsWord.width * DomainsKnownBits.tnum))
  (rw : BitsWord.width),
mul_dispatch_work
  (@snd DomainsKnownBits.tnum (CollectionsAuditCost.audit_trace unit)
     (mul_dispatch_source meet o args rw)) <=
numeric_envelope (numeric_kb_dimension o args rw).
```

### `DomainsAuditMulDispatch.mul_dispatch_total`

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMulDispatch.v`.

```rocq
Theorem mul_dispatch_total :
forall (meet : bool) (o : BitsOp.op) (args : list (BitsWord.width * DomainsKnownBits.tnum))
  (rw : BitsWord.width),
exists (result : DomainsKnownBits.tnum) (trace : CollectionsAuditCost.audit_trace unit),
  mul_dispatch_source meet o args rw = (result, trace).
```

### `DomainsAuditMulDispatch.mul_dispatch_unique`

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMulDispatch.v`.

```rocq
Theorem mul_dispatch_unique :
forall (meet : bool) (o : BitsOp.op) (args : list (BitsWord.width * DomainsKnownBits.tnum))
  (rw : BitsWord.width) (r1 : DomainsKnownBits.tnum)
  (t1 : CollectionsAuditCost.audit_trace unit) (r2 : DomainsKnownBits.tnum)
  (t2 : CollectionsAuditCost.audit_trace unit),
mul_dispatch_source meet o args rw = (r1, t1) ->
mul_dispatch_source meet o args rw = (r2, t2) -> r1 = r2 /\ t1 = t2.
```

### `DomainsAuditMulSource.mul_dom8_source_erases`

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMulSource.v`.

```rocq
Theorem mul_dom8_source_erases :
forall (w : BitsWord.width) (a b : DomainsKnownBits.tnum),
@fst DomainsKnownBits.tnum (CollectionsAuditCost.audit_trace unit) (mul_dom8_source w a b) =
DomainsKnownBitsFast.tnum_mul_precise w a b.
```

### `DomainsAuditMulDispatch.mul_precise_forward_erases`

Card: AUD-DM

Source destination: `theories/Domains/DomainsAuditMulDispatch.v`.

```rocq
Theorem mul_precise_forward_erases :
forall (o : BitsOp.op) (args : list (BitsWord.width * DomainsKnownBits.tnum))
  (rw : BitsWord.width),
@fst DomainsKnownBits.tnum (CollectionsAuditCost.audit_trace unit)
  (mul_precise_forward_source o args rw) =
@DomainsNumeric.pforward DomainsKnownBits.tnum DomainsKnownBitsFast.known_bits_precise_domain o
  args rw.
```

### `DomainsAuditProductSource.product_bits_round_source_bound`

Card: AUD-DR-PRODUCT

Source destination: `theories/Domains/DomainsAuditProductSource.v`.

```rocq
Theorem product_bits_round_source_bound :
forall (w : positive) (a : DomainsKnownBits.tnum) (b : DomainsWrapped.wrapped),
let raw :=
  match b with
  | DomainsWrapped.WItv lo hi =>
      CollectionsAuditCost.audit_z_bits lo + CollectionsAuditCost.audit_z_bits hi
  | _ => 1
  end in
let size :=
  1 + Pos.to_nat w + CollectionsAuditCost.audit_z_bits (DomainsKnownBits.zeros a) +
  CollectionsAuditCost.audit_z_bits (DomainsKnownBits.ones a) + raw in
product_work
  (@snd (DomainsKnownBits.tnum * DomainsWrapped.wrapped)
     (CollectionsAuditCost.audit_trace unit) (product_bits_round_source w (a, b))) <=
Init.Nat.of_num_uint
  (Number.UIntDecimal
     (Decimal.D1
        (Decimal.D0
           (Decimal.D0
              (Decimal.D0 (Decimal.D0 (Decimal.D0 (Decimal.D0 (Decimal.D0 Decimal.Nil))))))))) *
(Pos.to_nat w + 1) * (Pos.to_nat w + 1) * (size + 1) * (size + 1).
```

### `DomainsAuditProductSource.product_bits_round_source_erases`

Card: AUD-DR-PRODUCT

Source destination: `theories/Domains/DomainsAuditProductSource.v`.

```rocq
Theorem product_bits_round_source_erases :
forall (w : BitsWord.width) (input : DomainsKnownBits.tnum * DomainsWrapped.wrapped),
@fst (DomainsKnownBits.tnum * DomainsWrapped.wrapped) (CollectionsAuditCost.audit_trace unit)
  (product_bits_round_source w input) =
DomainsProduct.product_bits_round w input.
```

### `DomainsAuditProductSource.product_pack_depth_bound`

Card: AUD-DR-PRODUCT

Source destination: `theories/Domains/DomainsAuditProductSource.v`.

```rocq
Theorem product_pack_depth_bound :
forall (p : positive) (negated : bool) (lo hi : Z),
@CollectionsAuditCost.audit_case_count unit 326
  (@snd Z (CollectionsAuditCost.audit_trace unit)
     (product_pack_source p (product_prefix_test_source negated lo hi))) <=
2 * Pos.size_nat p * Pos.size_nat p.
```

### `DomainsAuditReduceBits.reduce_bits_exchange_laws`

Card: AUD-DR

Source destination: `theories/Domains/DomainsAuditReduceBits.v`.

```rocq
Theorem reduce_bits_exchange_laws :
@audit_exchange_laws DomainsKnownBits.tnum DomainsWrapped.wrapped
  DomainsKnownBits.known_bits_domain DomainsWrapped.wrapped_domain DomainsKnownBits.tnum_gamma
  DomainsWrapped.wrapped_gamma reduce_bits_exchange.
```

### `DomainsAuditReduceBits.reduce_bits_rank_source_erases`

Card: AUD-DR

Source destination: `theories/Domains/DomainsAuditReduceBits.v`.

```rocq
Theorem reduce_bits_rank_source_erases :
forall (w : BitsWord.width) (input : DomainsKnownBits.tnum * DomainsWrapped.wrapped),
@fst N (CollectionsAuditCost.audit_trace unit) (reduce_bits_rank_source w input) =
reduce_bits_rank w input.
```

### `DomainsAuditReduceSource.reduce_plain_erases`

Card: AUD-DR

Source destination: `theories/Domains/DomainsAuditReduceSource.v`.

```rocq
Theorem reduce_plain_erases :
forall (P Q : Type) (D1 : DomainsNumeric.word_domain P) (D2 : DomainsNumeric.word_domain Q)
  (exchange : audit_exchange P Q) (w : BitsWord.width) (input : P * Q),
@fst (P * Q) (CollectionsAuditCost.audit_trace (reduce_call P Q))
  (@audit_reduce_source P Q D1 D2 exchange w input) =
@audit_reduce P Q D1 D2 exchange w input.
```

### `DomainsAuditTransferSource.sb_choices_source_erases`

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransferSource.v`.

```rocq
Theorem sb_choices_source_erases :
forall args : list (BitsWord.width * DomainsSignedBounds.signed_bounds),
@fst (list (list (BitsWord.width * DomainsSignedBounds.sb_half)))
  (CollectionsAuditCost.audit_trace unit) (sb_choices_source args) =
DomainsSignedBoundsDomain.sb_choices args.
```

### `DomainsAuditTransferBounds.sb_forward_source_bound`

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransferBounds.v`.

```rocq
Theorem sb_forward_source_bound :
forall (o : BitsOp.op) (args : list (BitsWord.width * DomainsSignedBounds.signed_bounds))
  (rw : BitsWord.width),
transfer_work
  (@snd DomainsSignedBounds.signed_bounds (CollectionsAuditCost.audit_trace unit)
     (sb_forward_source o args rw)) <=
numeric_envelope (numeric_sb_dimension o args rw).
```

### `DomainsAuditTransferSource.sb_forward_source_erases`

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransferSource.v`.

```rocq
Theorem sb_forward_source_erases :
forall (o : BitsOp.op) (args : list (BitsWord.width * DomainsSignedBounds.signed_bounds))
  (rw : BitsWord.width),
@fst DomainsSignedBounds.signed_bounds (CollectionsAuditCost.audit_trace unit)
  (sb_forward_source o args rw) =
@DomainsNumeric.pforward DomainsSignedBounds.signed_bounds
  DomainsSignedBoundsDomain.signed_bounds_domain o args rw.
```

### `DomainsAuditTransferSource.transfer_choices_count`

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransferSource.v`.

```rocq
Theorem transfer_choices_count :
forall args : list (BitsWord.width * DomainsSignedBounds.signed_bounds),
@length (list (BitsWord.width * DomainsSignedBounds.sb_half))
  (@fst (list (list (BitsWord.width * DomainsSignedBounds.sb_half)))
     (CollectionsAuditCost.audit_trace unit) (sb_choices_source args)) =
2 ^ @length (BitsWord.width * DomainsSignedBounds.signed_bounds) args.
```

### `DomainsAuditTransferSource.transfer_fallback`

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransferSource.v`.

```rocq
Theorem transfer_fallback :
forall (o : BitsOp.op) (args : list (BitsWord.width * DomainsSignedBounds.signed_bounds))
  (rw : positive),
@fst bool (CollectionsAuditCost.audit_trace unit) (transfer_guard_source o args rw) = false ->
@fst DomainsSignedBounds.signed_bounds (CollectionsAuditCost.audit_trace unit)
  (transfer_forward_source o args rw) =
@DomainsNumeric.pforward DomainsSignedBounds.signed_bounds
  DomainsSignedBoundsDomain.signed_bounds_domain o args rw.
```

### `DomainsAuditTransferSource.transfer_forward_plain_erases`

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransferSource.v`.

```rocq
Theorem transfer_forward_plain_erases :
forall (o : BitsOp.op) (args : list (BitsWord.width * DomainsSignedBounds.signed_bounds))
  (rw : positive),
@fst DomainsSignedBounds.signed_bounds (CollectionsAuditCost.audit_trace unit)
  (transfer_forward_source o args rw) =
audit_div_one_forward o args rw.
```

### `DomainsAuditTransferSource.transfer_guard_erases`

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransferSource.v`.

```rocq
Theorem transfer_guard_erases :
forall (o : BitsOp.op) (args : list (BitsWord.width * DomainsSignedBounds.signed_bounds))
  (rw : positive),
@fst bool (CollectionsAuditCost.audit_trace unit) (transfer_guard_source o args rw) =
match o with
| BitsOp.bvsdiv =>
    match args with
    | @nil _ => false
    | (wa, _) :: @nil _ => false
    | (wa, _) :: (wb, b) :: @nil _ =>
        (2 <=? rw)%positive && (wa =? rw)%positive && (wb =? rw)%positive &&
        @OrderLattice.leb DomainsSignedBounds.signed_bounds
          (DomainsSignedBoundsDomain.signed_bounds_lattice rw) b
          (DomainsSignedBoundsDomain.signed_bounds_const rw 1) &&
        negb
          (@OrderLattice.leb DomainsSignedBounds.signed_bounds
             (DomainsSignedBoundsDomain.signed_bounds_lattice rw) b
             {|
               DomainsSignedBounds.sb_zero := DomainsSignedBounds.SBEmpty;
               DomainsSignedBounds.sb_one := DomainsSignedBounds.SBEmpty
             |})
    | (wa, _) :: (wb, b) :: _ :: _ => false
    end
| _ => false
end.
```

### `DomainsAuditTransferBounds.transfer_guard_source_bound`

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransferBounds.v`.

```rocq
Theorem transfer_guard_source_bound :
forall (o : BitsOp.op) (args : list (BitsWord.width * DomainsSignedBounds.signed_bounds))
  (rw : positive),
transfer_work
  (@snd bool (CollectionsAuditCost.audit_trace unit) (transfer_guard_source o args rw)) <=
numeric_envelope (numeric_sb_dimension o args rw).
```

### `DomainsAuditTransferBounds.transfer_source_bound`

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransferBounds.v`.

```rocq
Theorem transfer_source_bound :
forall (o : BitsOp.op) (args : list (BitsWord.width * DomainsSignedBounds.signed_bounds))
  (rw : positive),
transfer_work
  (@snd DomainsSignedBounds.signed_bounds (CollectionsAuditCost.audit_trace unit)
     (transfer_forward_source o args rw)) <=
numeric_envelope (numeric_sb_dimension o args rw).
```

### `DomainsAuditTransferSource.transfer_total`

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransferSource.v`.

```rocq
Theorem transfer_total :
forall (o : BitsOp.op) (args : list (BitsWord.width * DomainsSignedBounds.signed_bounds))
  (rw : positive),
exists (r : DomainsSignedBounds.signed_bounds) (t : CollectionsAuditCost.audit_trace unit),
  transfer_forward_source o args rw = (r, t).
```

### `DomainsAuditTransferSource.transfer_unique`

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransferSource.v`.

```rocq
Theorem transfer_unique :
forall (o : BitsOp.op) (args : list (BitsWord.width * DomainsSignedBounds.signed_bounds))
  (rw : positive) (r1 : DomainsSignedBounds.signed_bounds)
  (t1 : CollectionsAuditCost.audit_trace unit) (r2 : DomainsSignedBounds.signed_bounds)
  (t2 : CollectionsAuditCost.audit_trace unit),
transfer_forward_source o args rw = (r1, t1) ->
transfer_forward_source o args rw = (r2, t2) -> r1 = r2 /\ t1 = t2.
```

### `DomainsAuditTransferBounds.transfer_whole_execution`

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransferBounds.v`.

```rocq
Theorem transfer_whole_execution :
forall (o : BitsOp.op) (args : list (BitsWord.width * DomainsSignedBounds.signed_bounds))
  (rw : positive),
exists
  (result : DomainsSignedBounds.signed_bounds) (trace : CollectionsAuditCost.audit_trace unit),
  transfer_forward_source o args rw = (result, trace) /\
  transfer_work trace <= numeric_envelope (numeric_sb_dimension o args rw).
```

### `DomainsAuditWidenSource.widen_reduce_nodes`

Card: AUD-DW

Source destination: `theories/Domains/DomainsAuditWidenSource.v`.

```rocq
Theorem widen_reduce_nodes :
forall (w : BitsWord.width) (sign : bool) (half : DomainsSignedBounds.sb_half),
@CollectionsAuditCost.audit_case_count unit 233
  (@snd DomainsSignedBounds.sb_half (CollectionsAuditCost.audit_trace unit)
     (widen_reduce w sign half)) <=
1 + 4 * Pos.to_nat w.
```

### `DomainsAuditTransferBounds.word_eval_source_bound`

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransferBounds.v`.

```rocq
Theorem word_eval_source_bound :
forall (o : BitsOp.op) (args : list BitsWord.word),
word_source_work
  (@snd (option BitsWord.word) (CollectionsAuditCost.audit_trace unit)
     (word_eval_source o args)) <=
numeric_envelope (numeric_word_dimension o args).
```

### `DomainsAuditTransferWord.word_eval_source_erases`

Card: AUD-DT-WORD

Source destination: `theories/Domains/DomainsAuditTransferWord.v`.

```rocq
Theorem word_eval_source_erases :
forall (o : BitsOp.op) (values : list BitsWord.word),
@fst (option BitsWord.word) (CollectionsAuditCost.audit_trace unit) (word_eval_source o values) =
BitsOp.eval_op o values.
```

### `DomainsAuditTransferWrapped.wr_forward_erases`

Card: AUD-DT-WRAPPED

Source destination: `theories/Domains/DomainsAuditTransferWrapped.v`.

```rocq
Theorem wr_forward_erases :
forall (o : BitsOp.op) (args : list (BitsWord.width * DomainsWrapped.wrapped))
  (rw : BitsWord.width),
@fst DomainsWrapped.wrapped (CollectionsAuditCost.audit_trace unit) (wr_forward o args rw) =
DomainsWrapped.wrapped_forward o args rw.
```

### `DomainsAuditTransferBounds.wr_forward_source_bound`

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransferBounds.v`.

```rocq
Theorem wr_forward_source_bound :
forall (o : BitsOp.op) (args : list (BitsWord.width * DomainsWrapped.wrapped))
  (rw : BitsWord.width),
wr_work
  (@snd DomainsWrapped.wrapped (CollectionsAuditCost.audit_trace unit) (wr_forward o args rw)) <=
numeric_envelope (numeric_wr_dimension o args rw).
```

### `DomainsAuditTransferWrapped.wr_helpers_erases`

Card: AUD-DT-WRAPPED

Source destination: `theories/Domains/DomainsAuditTransferWrapped.v`.

```rocq
Theorem wr_helpers_erases :
(forall (w : BitsWord.width) (a b : DomainsWrapped.wrapped),
 @fst DomainsWrapped.wrapped (CollectionsAuditCost.audit_trace unit) (wr_mul w a b) =
 DomainsWrapped.wrapped_mul w a b) /\
(forall (w : BitsWord.width) (a : DomainsWrapped.wrapped),
 @fst (DomainsInterval.interval * DomainsInterval.interval)
   (CollectionsAuditCost.audit_trace unit) (wr_parts w a) =
 DomainsWrapped.wrapped_parts w a) /\
(forall (w : BitsWord.width) (a b : DomainsWrapped.wrapped),
 @fst DomainsWrapped.wrapped (CollectionsAuditCost.audit_trace unit) (wr_join w a b) =
 DomainsWrapped.wrapped_join w a b).
```

### `DomainsAuditTransferBounds.wr_source_total`

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransferBounds.v`.

```rocq
Theorem wr_source_total :
forall (o : BitsOp.op) (args : list (BitsWord.width * DomainsWrapped.wrapped))
  (rw : BitsWord.width),
exists (r : DomainsWrapped.wrapped) (t : CollectionsAuditCost.audit_trace unit),
  wr_forward o args rw = (r, t).
```

### `DomainsAuditTransferBounds.wr_source_unique`

Card: AUD-DT

Source destination: `theories/Domains/DomainsAuditTransferBounds.v`.

```rocq
Theorem wr_source_unique :
forall (o : BitsOp.op) (args : list (BitsWord.width * DomainsWrapped.wrapped))
  (rw : BitsWord.width) (r1 : DomainsWrapped.wrapped)
  (t1 : CollectionsAuditCost.audit_trace unit) (r2 : DomainsWrapped.wrapped)
  (t2 : CollectionsAuditCost.audit_trace unit),
wr_forward o args rw = (r1, t1) -> wr_forward o args rw = (r2, t2) -> r1 = r2 /\ t1 = t2.
```

### Public widening rank

Card: AUD-DW

Source destination: `theories/Domains/DomainsAuditWiden.v`.

```rocq
Definition audit_widen_rank (w : width) : bounded_widening_rank (audit_widen_lattice w) :=
  audit_widen_rank_builder audit_widen_rank_stable audit_widen_post_reduction_rank
    audit_widen_bounded w.

Theorem audit_widen_rank_measure : forall w a,
  wrank (base_wrank (audit_widen_rank w)) a = audit_widen_measure w a /\
  wbound (audit_widen_rank w) = 2%nat.
```

<!-- AUD-API-NUM-END -->
