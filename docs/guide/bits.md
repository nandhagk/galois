# Bits

Bits represents a dynamic word as a positive width and an integer.
[`wrap`](../../theories/Bits/BitsWord.v#L18) reduces that integer modulo the width's
power of two. `is_word` states the unsigned range, and `signed` gives the two's complement
interpretation. For example, the eight-bit representation of negative one is 255.
<!-- Source: BitsWordTest.word_boundaries. -->
The arithmetic and testbit theorems accept arbitrary integers wherever their statements
omit an `is_word` premise.

## Word functions and counts

[`BitsFun`](../../theories/Bits/BitsFun.v#L12) supplies total arithmetic, bitwise operations,
shifts, rotations, comparisons and counts. Unsigned division by zero gives all ones.
Signed division by zero gives one for a negative dividend and all ones otherwise.
Remainder by zero preserves the wrapped dividend.
Signed remainder follows truncating division, and signed modulus follows flooring division.
Shift amounts are wrapped at the operand width before the large-shift test.
Rotations then reduce their amounts modulo the width.
Leading-zero and trailing-zero counts of zero equal the width.

[`wpopcnt`](../../theories/Bits/BitsFun.v#L121) traverses the binary digits of the wrapped
value. `popcount_testbit` proves agreement with the low-bit filter count for every
nonnegative integer below the corresponding power of two.
`wpopcnt_spec` specializes that theorem to words.
`popcount_cost` states that `popcount_steps_pos p` equals `Pos.size_nat p`, including the
leading digit. This is a structural recursion-step count for the pure arithmetic function.
It does not measure native time or charge integer arithmetic.

## One operator table

[`op_desc`](../../theories/Bits/BitsOp.v#L152) is the sole operator dispatch table.
A descriptor holds an action, a kind, a commutativity flag and a constructor-and-parameter
code. The action derives `Desc.arity`, `Desc.result_width` and `Desc.value`.
The helpers are `unary`, `binary`, `compare`, `select`, `resize` and `concat`.
`Desc.wf` is a separate arity law.
`Desc.word_valued` is a separate conditional law for raw values.
Sign extension can have a negative raw value, so its final wrap remains necessary.

`eval_op` checks widths, normalizes operands and wraps the result.
Its public theorems cover failure, result width, arity, unsigned range, normalization and
marked commutativity. `word_fun1`, `word_fun2`, `word_cmp` and their evaluation theorems
remain available as views of the descriptor action.
`op_encoding` uses Base's pair codecs through a costed `encoding_comap`.
`op_encoding_laws` proves injectivity separately, and `op_encoding_cost` retains the
pair serializer's charge and the conversion overhead.

Add an operator by adding its constructor and one entry in `op_desc`.
Choose an existing helper, its kind, a fresh code tag and the correct symmetry flag.
The computational projections need no edits.
Prove any new word-function facts needed by the table's proof cases.
Extend the representative fixtures and the temporary legacy adapter when applicable.
[`op_cases`](../../theories/Bits/BitsTactics.v#L11) splits constructors and removes only
the cases that the client's `op_default` solves.
The `by` form supplies a default explicitly, and `kind_cases` provides the same contract
for descriptor kinds.

## Generic expressions and bridges

[`Expr.t O`](../../theories/Bits/BitsExpr.v#L18) is parametric in the operator carrier.
`Expr.eval ev env e` and `Expr.eval_args ev env es` use the supplied evaluator.
`Expr.env_of d xs` makes the missing-variable default explicit.
`expr` abbreviates `Expr.t op`.
`bridge_op_expr` transports a successful operator bridge to an expression bridge when
the target evaluator enforces arity and client values map to unsigned words.
`bridge_op_expr_bits` supplies Bits' arity theorem.
The bridge environment uses a one-bit zero default.
[`BitsBridge`](../../theories/Bits/BitsBridge.v#L80) also contains the expression-dependent
extension, truncation and concatenation theorems.

The [differential grid](../../tests/legacy/Bits/BitsOpLegacyTest.v#L126) checks every operator
against legacy evaluation, width checking, arity, commutativity and code.
It samples widths one, two, three and eight and raw values around zero and each modulus,
plus 255 and 1000. It includes malformed arities, width mismatches, valid selections and
parameter boundaries. The word-function comparison covers every pair of four-bit values
and population count on every ten-bit value.
<!-- Sources: BitsOpLegacyTest.widths, samples, grid and parameter_cases;
     BitsFunLegacyTest.word_functions_agree and popcount_width_ten_agrees. -->
These computed fixtures complement the universal theorems.
