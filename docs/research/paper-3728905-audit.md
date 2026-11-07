Copied from the pre-redesign research notes on 2026-11-07. Card and ruling IDs refer to the retired run.

# Audit of Fan et al. against DOM-9

Audit date: 2026-10-29. Primary source: Guangsheng Fan, Liqian Chen, Banghu Yin,
Wenyu Zhang, Peisen Yao and Ji Wang, “Program Analysis Combining Generalized Bit-Level
and Word-Level Abstractions,” *Proceedings of the ACM on Software Engineering* 2,
ISSTA, ISSTA030, July 2025, pp. 663–685, [DOI 10.1145/3728905](https://doi.org/10.1145/3728905).
The supplied local file `the supplied paper PDF` is the complete 23-page
article. Page references below are its article page numbers, which agree with PDF pages.

This is a source and mathematical audit, not a Rocq theorem, compiled execution or
performance experiment. It was independently reviewed with ACCEPT, subject to the
Theorem 6.2 scope clarification incorporated below, in `historical review paper-3728905-audit.md`.
It compares the C34 DOM-9 contract and
card at checkpoint `5a97d28`, the earlier research and review, the paper's formulas, and
selected landed DOM-2, DOM-3 and DOM-8 sources. Text extraction covered the article;
the original rendered pages 14–15 were also inspected for the critical formulas and
proof. The PDF has zero embedded files. Its §§4–5 refer to supplementary material,
which is not in the supplied PDF; the [Zenodo record](https://zenodo.org/records/14024794)
lists source archives, experimental data and a README, but no separately identified
supplementary paper. The artifact source is useful evidence of that implementation, not a
substitute for the missing full transfer specifications. Claims about artifact internals
below cite paths and line numbers in `clam-master.zip`, not transplanted source.

## Main finding: stated optimality and displayed reduction differ

Paper §2, p. 4, defines the standard reduced product of two abstractions as each
component's least abstraction of the intersection of the two concretizations. Section
6.1, p. 14, says its three exchanges realize this operator; §6.2, p. 15, calls the result
optimal. It also describes optimality in terms of no further improvement through component
cooperation. The actual proof argues that applying the same range-to-tnum exchange again
does not improve the mask. That restricted form of stability does not by itself entail
least component abstractions of the actual intersection.

The printed §6.1 formula is unambiguous. For one sign hemisphere and nonempty
tnum `T=(v,m)`, interval `I=[l,u]`, the operations are:

1. `I'=[max(l,v), min(u,v+m)]`;
2. `T'=T meet tnum_range(I'.lo,I'.hi)`;
3. `I''=[max(I'.lo,T'.v), min(I'.hi,T'.v+T'.m)]`.

The paper defines `tnum_range` on p. 5 as the common high prefix of the two endpoints
with every bit at and below their highest differing bit unknown. Mask meet on p. 7 is
the ordinary bitwise intersection, bottom on conflicting known bits. The artifact's
`switv_stnum_domain.hpp` lines 142–191 follows the same three exchanges for the first
hemisphere. The formula is thus no longer an inference from artifact code alone.

Counterexample to the standard reduced-product claim: width 4, zero hemisphere,
`T=0?00` representing `{0,4}`, `I=[1,6]`. Then `I'=[1,4]`,
`tnum_range(1,4)=0???`, `T'=0?00`, and `I''=[1,4]`. The intersection is `{4}`;
both least component abstractions are singleton 4. Repeating the displayed exchanges
does not change the result. All inputs are valid, nonempty, within one hemisphere,
and no special operation or undefined value is involved. This example refutes the
stated identification of these formulas with the standard component-hull reduction;
it does not show that the displayed exchanges are unsound, nor does it disprove
stability under those exchanges. DOM-9's explicit exact-hull specification is strictly
stronger on this example and remains a proof obligation, not an established theorem.

There is a separate issue with the stated auxiliary Theorem 6.2 on p. 15: it states
`tnum_range(I''.lo,I''.hi) = tnum_range(I'.lo,I'.hi)` without a case premise. Take
width 4, `T=0?00`, `I=[0,3]`: `I'=[0,3]`, `T'=0000`, `I''=[0,0]`; the two range
abstractions are `00??` and `0000`. The prose immediately before the theorem says its proof
assumes both endpoints are updated in the first and third steps and suggests the remaining
cases follow similarly. This input falls outside that contextual assumption: it refutes the
unrestricted displayed equality and its suggested extension, not the assumption-scoped claim.
The weaker mask equality used in the subsequent proof still holds in this example.
This observation therefore does not establish failure of exchange stability in general.

## Representation, operations, and scope

Paper §§4.1–4.2, pp. 7–11, use a tnum `(value,unknown-mask)` plus bottom, then one tnum
per sign. Fig. 5 applies binary component operations to all sign pairs, splits results
by sign and joins them. Section 5 and Fig. 7, pp. 11–13, independently apply interval
operations to sign pairs, split and join. Section 6 reduces the product afterward.
DOM-9 also keeps a mask and bounds per sign, but its required branch-pair lifting applies
both landed components to each *same operand-hemisphere combination* before joining and
reducing. That structure can retain cross-component correlation that independently joining
the paper components first may lose; this is a structural distinction, not a general
precision ordering. DOM-9's exact reduction acts after the specified joins, and cannot
recover information already lost by a component transfer or join.

| Operation or feature | Paper and artifact evidence | DOM-9 contract and comparison |
| --- | --- | --- |
| Add, subtract, negate | The paper generalizes kernel tnum arithmetic (§§2, 4.1), uses hemisphere-pair wrapped bounds (§5.2), and reports overflow-aware word bounds relative to the kernel. Full algorithms are not printed. | DOM-2 has carry-based add/sub and negation; DOM-3 has wrapping bounds. Similar ingredients do not establish matching outputs for every input. |
| Multiply | The paper cites the earlier tnum multiplication and does not print its detailed formula. The artifact `tnum_impl.hpp:828–856` uses a partial-product accumulation. | DOM-9 explicitly calls DOM-2, whose nonconstant `tnum_mul` keeps only low known-zero bits (`DomainsKnownBits.v:751–757`), plus DOM-3 wrapped multiplication. The optional landed DOM-8 precise multiplier is a different selectable domain and is not specified as DOM-9's component. The concrete witness below shows a loss relative to this artifact. |
| Unsigned divide | Fig. 4, p. 8, sets high quotient bits from `(vP+mP)/vQ`, returning top if `vQ=0`; §4.2 separately splits by sign. | DOM-2 supplies leading-zero quotient bounds with a nonzero-known-bit test; DOM-3 supplies bounds. Zero-divisor behavior must follow Bits' total semantics, so compare exact cases before treating the paper routine as a drop-in transfer. No blanket dominance established. |
| Signed divide, remainders | Table 2 and §4.1 list signed and unsigned division and remainder but refer most algorithms to the missing supplement. The artifact has respective helpers. | DOM-2 uses top for signed division, coarse dividend-derived unsigned remainder and a sign fact for signed remainder; DOM-3 contributes sign-split bounds. This identifies potential differences, not a proved whole-product precision ordering. |
| AND, OR, XOR, NOT | Paper tnum+ inherits bit operations; §5.2 returns top for word-level bit-vector cases other than truncation and extension. | DOM-2 supplies bitwise operations; DOM-3's bound transfers and the pair reduction may retain more bounds. Need case-specific comparison, including semantics and branching. |
| Shifts and rotations | Table 2 and §4.1 add variable shifts; other details are deferred. Artifact `tnum_impl.hpp:1270–1318` joins every integer amount from minimum to maximum for variable logical right shift, without filtering against amount mask. The paper does not document rotations in this table. | DOM-2's factored transfer joins precisely the constant transfers for allowed amount words (`tnum_variable_join`); DOM-9 uses it with DOM-3. A concrete reverse precision witness appears below. Rotation semantics and oversized shifts are Gaulois contract additions; absence from the printed table is not proof the artifact lacks them. |
| Truncation, zero/sign extension | §4.1, pp. 8–9, gives bitwise truncation explicitly; §5.2 says bounds implement truncation and extension. | DOM-2 maps bits and DOM-3 projects wrapped bounds; DOM-9 handles output hemisphere split and differing widths. Full parity is unverified. |
| Comparison and tests | §4.1, p. 9, gives unsigned `<=` refinement through extrema and `tnum_range`; §§4.2 and 5.2 adapt it to sign pairs. Other cases are not fully printed. | DOM-2 and DOM-3 provide their own `passume`; DOM-9 additionally branches on the result and intersects each returned operand with its original branch. Paper test refinement is not automatically equal to this general backward operator. |
| Join and widening | Fig. 5 joins sign masks; Fig. 7 uses component interval joins and per-hemisphere doubling widening. §4.1 and §4.2 describe a special trailing-bit widening, although Fig. 5 shows mask join. | DOM-9 uses join as widening and a bounded rank; the paper's acceleration is not part of its contract. Different widening affects convergence and results, without an established universal ordering. |
| Counts, extract, concat, `ite`, malformed shapes | These are not specified in the relevant printed tables and discussion. | DOM-9 composes the existing Bits/DOM-2/DOM-3 interfaces and their sound fallbacks; three-operand `ite` requires up to eight branches, and malformed shapes must preserve the contract's length/refinement guarantees. No paper parity assertion follows. |

The paper uses both the motivating split and non-relational machine-word abstractions, not
an assurance that its complete transfer suite is individually optimal. Its §6.2 claim is
about reduction, not optimality of arbitrary forward or backward operations. Section 6.2's
`O(n)` counts program variables; it does not give a parameterized bit-complexity or
whole-analysis convergence bound. The earlier research's bigint caveat remains applicable.

### Two narrow transfer witnesses

These are hand calculations from cited source and the current stated composition; they are
not executable tests, proofs of global dominance, or claims about every implementation of
the paper. All mentioned shift counts are less than the operand width.

* Multiply: 5-bit `x={1,3}` has tnum `(v=1,m=2)` and bounds `[1,3]`; `y=3` is a
  singleton. The artifact's partial-product multiplier yields `(v=1,m=14)`; the
  nonwrapping interval result is `[3,9]`, yielding the product intersection
  `{3,5,7,9}`. The artifact sign-pair wrapper, interval helper and product reduction are in
  `stnum_impl.hpp:1059–1073`, `swrapped_interval_impl.hpp:110–138,1580–1629`, and
  `switv_stnum_domain.hpp:414–417`. DOM-2's nonconstant multiplication has no trailing zero
  fact here,
  hence its mask is top; together with the same bounds DOM-9's specified combination
  yields `[3,9]`, containing even results 4, 6 and 8 as well. Exact reduction does not
  repair that loss: its input intersection already contains them. Concrete results are
  `{3,9}`. DOM-8's selectable partial-product multiplier is already stronger than
  DOM-2 here; its use in DOM-9 would be a scope change requiring an owner decision.
* Logical right shift: width 8, dividend singleton 64 and amount tnum `00000?00`, with
  amounts `{0,4}` and bounds `[0,4]`. The artifact tnum helper joins scalar shifts
  for every amount 0 through 4, including 1 and hence 32; the artifact variable-shift
  interval helper returns top and reduction retains 32 (`stnum_impl.hpp:1241–1255`,
  `swrapped_interval_impl.hpp:1856–1868`, `switv_stnum_domain.hpp:414–417`). The paper
  describes a word-level bit-vector top fallback but does not print this tnum shift helper.
  DOM-2 instead joins only amounts 0 and 4,
  obtaining the tnum hull of `{64,4}` (`0?000?00`), which excludes 32; any conjunction
  with the wrapped result still excludes it. This comparison concerns the described
  fallback and artifact helper, not an unprinted supplemental transfer algorithm.

The previously circulated witness `{0,2} * 3` is withdrawn: the artifact mask `0110`
represents `{0,2,4,6}`, so it cannot demonstrate exclusion of 4.

## Proposed documentation corrections, for owner review only

No tracked documentation, API, card, source, branch or index was changed in this audit.
The following are replacement fragments, not an authorization to modify a contract:

* In `historical research note combined-bit-domain-2025.md` evidence and limits, replace the 403 /
  unavailable-primary-PDF statements with: “The owner supplied the complete 23-page
  article PDF. Its §§2 and 6.1–6.2 define and claim standard reduced-product optimality,
  display all three exchanges, and give the proof discussed below. The referenced
  supplementary transfer details are not bundled in the PDF or separately identified
  in the Zenodo record; the artifact gives implementation evidence, not complete paper
  transfer specifications.”
* Replace the artifact-only characterization of the counterexample with: “The printed
  middle exchange is tnum meet with `tnum_range` of the first-clamped interval. For
  `T=0?00` and `[1,6]`, the three printed steps yield `T=0?00`, `[1,4]`, although the
  intersection is `{4}`. Section 2 defines standard reduction by least abstractions of
  the intersection and §6.1 claims to realize it. Section 6.2's proof instead argues
  that further exchanges of the same form do not improve the result. This example is a
  mathematical counterexample to the claimed standard reduction, not to soundness or to
  the narrower fixed-point statement.” Include the Theorem 6.2 counterexample separately.
* In the DOM-9 card's read-first and scope text, replace “inaccessible publisher formulas”
  and “undocumented complete transfers” with the actual state: inspected main-paper
  formulas, missing supplement, and independently implemented artifact evidence. Keep
  exact-hull reduction, DOM-2/DOM-3 reuse, all theorem statements, and C34 intact unless
  the owner rules otherwise. Add the multiply and shift witnesses as optional future
  precision research, not new completion conditions.
* Review the retired domains API contract, the retired design overview, and C34's descriptions with the above
  evidence: “stronger reduction” is supported by the displayed counterexample; it does
  not establish implementation correctness or comprehensive transfer parity. No false
  DOM-9 public theorem statement was identified in this source audit. No API change is
  proposed as a C14 correction. A decision to select DOM-8 multiplication, add different
  widening, or promise any paper transfer parity changes scope and requires owner review.

No authored-code skill applied: this is a research-only Markdown audit with no code edit.
