# Base

Base provides positive key encodings, decoders, reflected equality, labelled paths and
certification. Its computational dictionaries contain data and functions. Separate `Prop`
records state injectivity, decoder round trips and numeric cost assumptions. A client can
compute keys without supplying any of these proofs.

## Encodings and codecs

An [`encoding K`](../../theories/Base/BaseEncoding.v#L12) supplies
`encode_c : K -> Cost.t positive`. The pure accessor `encode E x` returns its `Cost.value`.
`key_bits E x` counts every binary digit, including the leading digit. The record
`encoding_laws E` supplies `encode_injective`. It says that equal codes imply equal keys.

A [`codec K`](../../theories/Base/BaseEncoding.v#L52) adds
`decode : positive -> option K`. Its separate `codec_laws` record supplies `decode_encode`.
The theorem `codec_laws_injective` derives the encoding law from that round trip.
A decoder may accept additional codes. The law requires it to recover every encoded value.

The scalar codecs are `positive_codec`, `N_codec`, `nat_codec`, `Z_codec`, `bool_codec` and
`unit_codec`. Each has a `_laws` theorem and an encoding alias such as `nat_encoding`.
Each alias has separate `_laws` and `_cost_laws` theorems.
Scalars retain the legacy layouts. Positive numbers encode as themselves, naturals as their
positive successor, and signed numbers use low-bit sign tags. Booleans use one for false and
two for true. Unit uses one. Boolean and unit decoders reject other codes.

`of_pure f` lifts a pure word-RAM primitive at one tick per call. Use it when that primitive
cost convention is appropriate. Use a costed encoding directly for a traversal or callback
whose work depends on its input.

## Derive a client codec

The universal [`code`](../../theories/Base/BaseCode.v#L15) has `Atom positive` and
`Node (list code)` constructors. A client supplies a costed conversion
`to_code : T -> Cost.t code`, a partial conversion `of_code : code -> option T`, and a proof
`rt : forall x, of_code (Cost.value (to_code x)) = Some x`.
Then `derive to_code of_code rt` constructs a codec, and `derive_laws` proves its round trip.
The costed callback prevents the client conversion from hiding recursive work.

The [binary-tree client](../../tests/Base/BaseCodeTest.v#L15) is a complete checked example.
Leaves become atoms and branches become nodes holding two child codes.
Its conversion charges each recursion step.
The client proves its round trip with `solve_roundtrip` and passes that proof to `derive`.
Its tests include a recursive tree and a rejected node of the wrong arity.

The built-in `pair_codec`, `list_codec`, `option_codec` and `sum_codec` compute without
component laws. Their `_laws` theorems take the component codec laws.
Pairs and lists use nodes of component atoms. Options use an empty node for absence and a
single atom for presence. Sums use a single atom on the left and an extra nested node on the
right. Arbitrary component tick counts flow through these compositions.

## Serialization and costs

The serializer keeps the legacy delimited positive symbols and adds a tree grammar.
An atom begins with false and then emits its positive code. A node begins with true and then
emits its child list. A child list uses false for nil and true followed by a tree and the
rest of the list for cons. Positive symbols use false,false for a zero digit, true,true for a
one digit, and false,true for the final leading one. Bits run from least significant to most
significant. A final one converts the whole stream into a positive number.

`code_decode` parses with fuel equal to the stream length and rejects unused suffix bits.
`read_emit_tree` proves that the emitted structural weight supplies enough fuel.
`code_decode_encode` proves the decoder round trip constructively.
`code_encode_bits` gives the exact bit count as `1 + N.of_nat (code_weight c)`.
The weight counts tree tags, child-list tags and twice the atom digit counts.

Every emission and stream-construction recursion step charges a tick.
The serializer also runs `Cost.tick_bits` on its result.
The named constant [`encode_k`](../../theories/Base/BaseEncoding.v#L83) is `8`.
<!-- Source for constants and formulas: BaseEncoding.v and BaseCode.v cost theorems. -->
`code_encode_cost` bounds serialization by `encode_k` times the result bit count.
The constant is an overhead bound. It does not bound arbitrary component calls.

The separate record `encoding_cost_laws E k` states
`forall x, Cost.ticks (encode_c E x) <= k * key_bits E x`.
The generic composite `_cost` theorems expose component calls and serialization separately.
The `_encode_cost_le` theorems substitute explicit component numeric laws.
For component constants `ka`, `kb` and `k`, the resulting multipliers are as follows.

| Codec | Numeric multiplier on its result bits |
| --- | --- |
| Pair | `ka + kb + encode_k + 3` |
| List | `k + encode_k + 2` |
| Option | `k + encode_k + 2` |
| Sum | `ka + kb + encode_k + 2` |

The bit-size theorems justify these substitutions.
Pair output bits equal `7 + 2 * a + 2 * b` for component bit counts `a` and `b`.
List output bits equal `3 + 2 * length + 2 * total_component_bits`.
The option and sum size theorems give the corresponding branch-specific formulas.
`derive_encode_cost_le` additionally requires a bound on the client conversion.
`encoding_comap` likewise takes a costed conversion and exposes its cost independently.
Its injectivity theorem takes the conversion's injectivity as a separate premise.

The [differential fixtures](../../tests/legacy/Base/BaseEncodingLegacyTest.v#L16) compare
`[]`, `[1]`, `[1;2]`, `(1,2)`, `None` and `Some 3` with the legacy codes.
Both layouts distinguish the fixtures within each type.
The new layout uses at most six extra bits on these fixtures.
<!-- Source: differential_fixture_bits and differential_size_bounds in the fixture file. -->
This is a fixture bound. Lists of arbitrary length have tag overhead proportional to length.

## Equality and tactics

[`eqb`](../../theories/Base/BaseEq.v#L50) compares encoded keys.
`eqb_spec`, `eqb_true_iff` and `eqb_false_iff` connect its boolean result to equality under
`encoding_laws E`. Reflexivity and symmetry hold even for an unlawful dictionary.
`eqb_dec` supplies constructive decidable equality.
`eqb_c` charges both encoding callbacks and a synchronized traversal of the shorter code.
The digit traversal computes equality itself, so it does not hide a separate minimum or
comparison traversal.

Import `BaseKeyTactics` to use `case_key` and `solve_roundtrip`.
`case_key` finds `HE : encoding_laws E` and splits an `eqb E a b` or
`Pos.eqb (encode E a) (encode E b)` test in the goal or context.
Each branch keeps `a = b` or `a <> b` and rewrites matching tests.
It leaves substitutions to the caller.
`solve_roundtrip` inducts on the round-trip input, reduces constructor matches, and rewrites
induction hypotheses and component codec laws. Unsupported residue stays visible.
The [tactic clients](../../tests/Base/BaseKeyTacticsTest.v#L16) show both raw and wrapped tests.

## Paths and certification

[`Rel.lpath`](../../theories/Base/BaseRel.v#L13) records a path's labels in order.
Its lemmas support concatenation, induction from the final step, relation inclusion,
state and label mapping, and step-closed invariants.
`Rel.star` allows an empty traversal and `Rel.plus` requires at least one step.
`star_iff_lpath` connects closure to paths carrying unit labels.

[`certify`](../../theories/Base/BaseCertify.v#L12) takes a predicate, a boolean checker,
its soundness proof and a candidate. It returns a proof-carrying candidate when the checker
accepts and `None` when the checker rejects.
`certify_some_iff` characterizes successful certification.
`certify_or` returns a supplied certified fallback on rejection.
`certify_or_sound` proves that the returned candidate satisfies the predicate.
The checker needs soundness. Completeness is a separate client obligation when required.
