Copied from the pre-redesign research notes on 2026-11-07. Card and ruling IDs refer to the retired run.

# Signedness-aware combined bit and bound domain: evidence and decision

Guangsheng Fan, Liqian Chen, Banghu Yin, Wenyu Zhang, Peisen Yao and Ji Wang,
“Program Analysis Combining Generalized Bit-Level and Word-Level Abstractions,”
*Proceedings of the ACM on Software Engineering* 2, ISSTA (2025), 663–685,
<https://doi.org/10.1145/3728905>.

## Evidence and limits

The owner supplied the complete 23-page primary article at `~/Downloads/3728905.pdf`; its
section 2 (p. 4) and sections 6.1–6.2 (pp. 14–15) define and claim standard reduced-product
optimality, display the three exchanges and give the proof discussed below. The article refers
to supplementary material for full transfer details; that supplement is not embedded in the PDF
or separately identified in
the [Zenodo artifact record](https://zenodo.org/records/14024794), and has not been inspected.
The artifact's `clam-master.zip` supplies implementation evidence, not the missing complete
transfer specifications. The paper and the reduction counterexamples were independently
reviewed in `historical review paper-3728905-audit.md`. The calculations are not compiled executions
or kernel-checked claims. A claim of faithful reproduction of every paper algorithm remains
unsupported. The code must be independently authored, not copied from another library.

Sections 4.1–4.2 generalize tnums, retain a separate tnum for each sign hemisphere, and lift a
binary operation over hemisphere pairs. Section 5.1 uses a separate bounded interval per
hemisphere; its abstraction is incomparable with a single circular interval. Section 5.2 discusses
hemisphere-wise arithmetic, division and remainder, extension, truncation and test refinement;
other bit-vector word-level cases can return top. Section 6.1 describes three exchanges per
hemisphere: clamp interval to tnum extrema, meet tnum with a range abstraction of the interval,
and clamp again. Section 2 defines the standard reduced product as the least component
abstractions of the actual intersection, and section 6.1 says these steps realize it. Section
6.2's Theorem 6.3 calls the reduction optimal, but its proof argues that a further exchange of
the same form cannot improve the mask; it does not establish least component hulls or universally
best operation transfers.

There is a material distinction between exchange stability and least component abstractions of
the actual intersection. The printed middle exchange is an ordinary tnum meet with the interval's
standard bit hull. Let width be 4, T represent `{0,4}` and I be `[1,6]`. Clamp gives `[1,4]`,
the bit hull of `[1,4]` is `0???`, meeting it with T leaves `{0,4}`, and the final clamp leaves
`[1,4]`. Their intersection is `{4}`, whose two least component abstractions are singleton 4.
This independently reviewed mathematical counterexample refutes the paper's identification of
the displayed exchanges with standard least-component reduction; it does not refute soundness
or the narrower exchange-stability claim and is not a checked Rocq result.

Theorem 6.2 displays an unconditional equality between the range abstractions before and after
the final clamp. With width 4, `T=0?00`, `I=[0,3]`, the first range abstraction is `00??` and
the final one is `0000`. The prose immediately before the theorem says its proof assumes all
lower and upper bounds update in both clamp steps and suggests other cases follow similarly;
this example lies outside that assumption. It refutes the unrestricted displayed equality and
its suggested extension, not the statement under that proof assumption. The weaker mask equality
used subsequently still holds in this example.

The proposed Gaulois reduction strengthens the visible exchange method: search for the least and
greatest tnum-compatible values inside each interval, and use the tnum hull of that feasible
subrange to refine masks. It must prove the least-component property directly from the actual
word-restricted intersection. If the proof fails or a counterexample exists, stop and report;
do not weaken it to a fixed-point statement. This is a specified Gaulois adaptation, not an
assertion that the paper's exchange algorithm is identical. Full transfer parity remains
unverified while the referenced supplementary specifications are uninspected.

## Choice and integration

Add a selectable `word_domain`, its `tagged_domain`, and its capped form. DOM-1a supplies those
builders and laws, DOM-2 supplies tnums and known-bits operations, DOM-3 supplies wrapped
operations and the semantic support for finite intervals, and BIT-2 supplies word semantics.
The proposed domain computes each operand-hemisphere combination with existing component
transformers, splits results at the sign bit, joins corresponding output hemispheres, then
reduces. Soundness of those existing transfers composes; it does not inherit their optimality.
The pair-aware backward query similarly considers each operand/result hemisphere combination.
Operators omitted or treated more coarsely in the existing component domains remain sound, and
the public contract names the exact fallback. This is not a claim of paper-level transfer parity.

C32's `bits_wrapped_domain` has one tnum and one circular arc, and intentionally preserves
`WFull` for consistent masks. The two representations are incomparable: per-sign facts can
distinguish signed alternatives, while a circular arc can represent some same-sign wrapping
complements more tightly. DOM-4 and its worktree remain untouched. No new solver, native code,
benchmark gate, global instance, or extraction directive is needed.

For width value `w`, feasible-extremum search inspects at most `w` bit positions with a
most-significant-first tight-bound dynamic program or equivalent greedy construction. Count each
mask, comparison and shift as an arbitrary-precision operation on O(w)-bit operands; with simple
linear-cost primitives a search costs O(w²) bit operations, not O(1). A transfer makes a bounded
number of existing component calls (up to 2^arity, arity at most 3), plus normalization and
reduction; state the cost of those calls separately, especially variable shifts, multiplication
and division. Storage is O(w) bits per payload. A binary-encoded width takes O(log w) bits, so
linear work in the numeric width is exponential in its encoding length. Paper section 6's O(n)
in variable count assumes a per-variable cost model and does not establish fixed-cost bigint
operations or a whole-analysis complexity bound.
