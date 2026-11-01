# Galois.Float

The floating-point package, the only one that uses Flocq. It gives finite-float interval domains
over IEEE binary32 and binary64, a NaN-observability analysis, and float operators for the `Ssa`
toy. For example, `[1.0, 2.0]` plus `[1.0, 1.0]` is `[2.0, 3.0]` with no NaN, no zero and no
subnormal; and if no later instruction looks at the payload or the sign of a NaN, two runs that
differ only in NaN payloads behave the same, so a pass may replace one NaN by another.

Floats are not `Bits`: no operator here goes through the operator bridge, and a float operator has
its own soundness theorem. No other package imports `Float`; its card, FLT-1, is part of the build.
It depends on Order (lattices and meanings), Views (`sparse_domain`), Analyses (the demand
framework of ANA-4) and `Examples.Ssa`, which supplies `OExt`, `VF32` and `VF64`.

Conventions of this document:
- **Axioms.** A theorem of `Galois.Float` may depend on exactly these axioms and on no others:
  `Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec`,
  `Stdlib.Reals.ClassicalDedekindReals.sig_not_dec`,
  `Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`, and
  `Stdlib.Logic.Classical_Prop.classic`. The pinned Flocq operations and bit decoders inherit
  `classic` in addition to the classical real-number foundations. `galois check claims` must
  allow exactly this list for `Galois.Float` theorems. A theorem of any other package depends
  on no axiom. C56 records the owner's approval of `classic`; FLT-1 updates the checker.
- **Sections.** FloatInterval.v, FloatOps.v and FloatNan.v each open `Section Float` with
  `Context {prec emax : Z} {Hprec : Prec_gt_0 prec} {Hmax : Prec_lt_emax prec emax}` and
  `Notation fl := (binary_float prec emax)`, and close it at the end of the file. Everything is
  generic in `prec` and `emax`, which are implicit arguments; `@name 24 128` is the binary32
  instance and `@name 53 1024` the binary64 one. Argument conventions follow Flocq: `prec` and
  `emax` are explicit in `is_nan`, `B2R`, `B2FF` and `Bcompare`.
- **The `ext` argument.** Every `Ssa` definition takes `ext : nat -> list cval -> option cval`, the
  evaluation of `OExt tag`, as its first argument; examples.md omits it. In FloatSsa.v every Ssa
  definition is applied to `fx`, which stands for `float_ext nm32 nm64` for two NaN models, so
  every statement there quantifies over `nm32` and `nm64`.

## Files

| File | Contents | Card |
|---|---|---|
| `FloatInterval.v` | float intervals with NaN, signed-zero and subnormal flags; lattice, concretisation, top and widening rank | FLT-1 |
| `FloatOps.v` | NaN models, concrete and abstract operators, comparison refinement, soundness | FLT-1 |
| `FloatNan.v` | NaN observability as a demand domain, backward transfers | FLT-1 |
| `FloatSsa.v` | float operators in the `Ssa` toy, the value domain, the NaN demand view, the instantiation theorems | FLT-1 |

## Definitions

```coq
(* FloatInterval.v. Flocq 4 (From Flocq Require Import IEEE754.Binary). *)
Definition fle (x y : fl) : Prop :=
  match Bcompare prec emax x y with Some Lt | Some Eq => True | _ => False end.
(* The smallest normal number is 2^(2 - emax), 2^-1022 for binary64; a finite nonzero number of
   smaller magnitude is subnormal. *)
Definition subnormal (x : fl) : Prop :=
  is_finite prec emax x = true /\ B2R prec emax x <> 0%R /\
  (Rabs (B2R prec emax x) < bpow radix2 (2 - emax))%R.
Definition fl_nn : Type := {x : fl | is_nan prec emax x = false}.   (* a float that is not a NaN *)
Record fl_interval : Type := FlInterval {
  flo : fl_nn;               (* lower bound of the non-NaN, nonzero values; may be -inf *)
  fhi : fl_nn;               (* upper bound; may be +inf *)
  may_nan : bool;
  may_neg_zero : bool;
  may_pos_zero : bool;
  may_subnormal : bool       (* a nonzero subnormal may occur *)
}.
Definition fl_gamma (I : fl_interval) (x : fl) : Prop :=
  match B2FF prec emax x with
  | F754_nan _ _ => may_nan I = true
  | F754_zero s => (if s then may_neg_zero I else may_pos_zero I) = true
  | _ => fle (proj1_sig (flo I)) x /\ fle x (proj1_sig (fhi I)) /\
         (subnormal x -> may_subnormal I = true)
  end.
Definition fl_lattice : lattice fl_interval.
(* leb I J: every flag of I is a flag of J, and either I has no nonzero non-NaN value (flo I above
   fhi I) or its bounds lie within those of J; bot: flo = +inf, fhi = -inf, no flag; join: the
   smaller lower and the larger upper bound (an empty operand contributes none), flags or-ed;
   widen a b: a bound of b outside the bounds of a goes to infinity, flags or-ed; narrow a b: an
   infinite bound of a is replaced by that of b, the flags of a are kept *)
Definition fl_concretisation : concretisation fl_interval fl := Concretisation fl_gamma.
Definition fl_top : fl_interval.      (* flo = -inf, fhi = +inf, every flag set *)
Definition fl_top_lattice : top fl_lattice.      (* top_value = fl_top *)
Definition fl_widening_rank : bounded_widening_rank fl_lattice.
(* wrank I = (1 if flo I is not -inf) + (1 if fhi I is not +inf) + the number of flags of I that are
   false; wbound = 6. A widening step moves a bound to infinity or sets a flag. *)
```

```coq
(* FloatOps.v. Rounding is to nearest even. A NaN has a sign and a payload, and hardware decides
   which of an operation's NaN operands supplies them; that choice is a parameter. *)
Inductive farith : Type := FAdd | FSub | FMul | FDiv.       (* operators with a float result *)
Inductive fbop : Type := FArith (o : farith) | FLt.         (* FLt: x < y, integer result 1 or 0 *)
Record nan_model : Type := NanModel {
  nan_choice : farith -> fl -> fl -> fl;
  nan_choice_nan : forall o x y, is_nan prec emax (nan_choice o x y) = true;
  nan_choice_local : forall o x y x' y',
    is_nan prec emax x = is_nan prec emax x' -> is_nan prec emax y = is_nan prec emax y' ->
    (is_nan prec emax x = true -> B2FF prec emax x = B2FF prec emax x') ->
    (is_nan prec emax y = true -> B2FF prec emax y = B2FF prec emax y') ->
    nan_choice o x y = nan_choice o x' y';
  nan_neg : fl -> fl;
  nan_neg_nan : forall x, is_nan prec emax (nan_neg x) = true;
  nan_abs : fl -> fl;
  nan_abs_nan : forall x, is_nan prec emax (nan_abs x) = true
}.
(* The model whose every answer is the quiet NaN of payload 2^(prec - 2) and sign false. It makes
   the record inhabited, so no theorem about models is vacuous. A hardware model (the first NaN
   operand, quieted, on x86; the default NaN on Arm) is a client's definition with its own proof
   of the one law. *)
Definition default_nan_model (Hp : (2 <= prec)%Z) : nan_model.
Definition fl_eval_bin (nm : nan_model) (o : farith) (x y : fl) : fl.
(* Flocq's Bplus, Bminus, Bmult and Bdiv with mode_NE and, as the NaN choice,
   fun x y => exist _ (nan_choice nm o x y) (nan_choice_nan nm o x y) *)
Definition fl_eval_neg (nm : nan_model) (x : fl) : fl.
(* Flocq's Bopp with the NaN choice fun x => exist _ (nan_neg nm x) (nan_neg_nan nm x) *)
Definition fl_eval_abs (nm : nan_model) (x : fl) : fl.          (* Babs likewise, with nan_abs *)
Definition fl_lt (x y : fl) : bool :=
  match Bcompare prec emax x y with Some Lt => true | _ => false end.
Definition fl_bin (o : farith) (I J : fl_interval) : fl_interval.
(* interval arithmetic with outward rounding of the bounds (Flocq's mode_DN for the lower bound,
   mode_UP for the upper); may_nan when an operand may be NaN or an invalid operation is possible:
   inf - inf (inf + -inf), 0 * inf, 0 / 0 or inf / inf; zero flags by the signs of the bounds and
   the possibility of underflow to zero; may_subnormal when the nonzero result range reaches
   below the smallest normal number, bpow radix2 (2 - emax), in magnitude *)
Definition fl_neg (I : fl_interval) : fl_interval.      (* swaps the bounds and the zero flags *)
Definition fl_abs (I : fl_interval) : fl_interval.
Definition fl_assume_lt (I J : fl_interval) : fl_interval * fl_interval.
(* refine both operands under the assumption x < y, which is false when either is NaN: the upper
   bound of x is at most that of y, the lower bound of y at least that of x, neither may be NaN *)
```

```coq
(* FloatNan.v. Demand: not demanded at all, or demanded with the NaN sign and payload observed or
   not. A non-NaN value is always demanded exactly. *)
Inductive nan_demand : Type := NotDemanded | Demanded (sign payload : bool).
Definition ff_agree (sg pl : bool) (a b : full_float) : Prop :=
  match a, b with
  | F754_nan s1 p1, F754_nan s2 p2 => (sg = true -> s1 = s2) /\ (pl = true -> p1 = p2)
  | F754_nan _ _, _ => False
  | _, F754_nan _ _ => False
  | _, _ => a = b
  end.
Definition nan_agree (d : nan_demand) (x y : fl) : Prop :=
  match d with
  | NotDemanded => True
  | Demanded sg pl => ff_agree sg pl (B2FF prec emax x) (B2FF prec emax y)
  end.
Definition nan_domain : demand_domain nan_demand fl.
(* dlat: NotDemanded below Demanded false false below the two single-bit demands below
   Demanded true true; join is the least upper bound, widen = join, narrow a _ = a;
   dagree := Agreement nan_agree *)
Definition nan_back (o : fbop) (d : nan_demand) : nan_demand * nan_demand.
(* The demands on the two operands given the demand d on the result.
   NotDemanded gives (NotDemanded, NotDemanded). For a float result (FArith _): a demand of the
   sign or of the payload, Demanded true _ or Demanded _ true, gives Demanded true true on both
   operands, because the choice between two NaN operands depends on both of their signs and
   payloads; Demanded false false gives Demanded false false on both. For FLt the result is an
   integer, demanded exactly, and any Demanded value gives Demanded false false on both: a
   comparison sees whether an operand is NaN and nothing else about it. *)
```

```coq
(* FloatSsa.v. The Ssa toy is Flocq-free: it carries float bit patterns (VF32 and VF64) and one
   extension operator (OExt tag), evaluated by the `ext` argument of every Ssa definition. This file
   supplies `ext` and the analyses over it. *)
Inductive fw : Type := F32 | F64.
Definition float_ext_tag (w : fw) (o : fbop) : nat.
(* 2 * i + (0 for F32, 1 for F64), where i numbers FAdd, FSub, FMul, FDiv and FLt from 0 to 4 *)
Definition float_ext_decode (tag : nat) : option (fw * fbop).   (* the inverse; None from 10 on *)
Definition float_ext (nm32 : @nan_model 24 128) (nm64 : @nan_model 53 1024) :
  nat -> list cval -> option cval.
(* float_ext_decode tag gives (w, o), or the result is None. For w = F32 and the arguments
   [VF32 a; VF32 b] with a and b in [0, 2^32): for o = FArith o', VF32 (bits_of_b32 (fl_eval_bin nm32
   o' (b32_of_bits a) (b32_of_bits b))); for o = FLt, VInt W32 1 when fl_lt holds of the decoded
   operands and VInt W32 0 otherwise. F64 likewise with VF64, b64_of_bits, bits_of_b64 and nm64. A
   different arity or width, or an out-of-range pattern, gives None, and the toy traps. *)
Definition float_ext_sigs : list (nat * (list ty * ty)).
(* For each width, the four arithmetic tags take two operands of that width and return that
   width; the comparison tag takes two operands of that width and returns TyI32. *)

(* Facts about Ssa values: nothing, a binary32 interval, a binary64 interval, or any value. *)
Inductive fl_any : Type :=
  | FlBot
  | FlA32 (I : @fl_interval 24 128)
  | FlA64 (I : @fl_interval 53 1024)
  | FlOther.
Definition fl_any_lattice : lattice fl_any.
(* FlBot below everything; FlA32 I <= FlA32 J and FlA64 I <= FlA64 J as in fl_lattice, the two widths
   incomparable; everything below FlOther; the join of facts of two widths is FlOther; widen and
   narrow act within a width, and widening across widths gives FlOther *)
Definition fl_any_concretisation : concretisation fl_any cval.
(* FlBot contains nothing; FlA32 I contains VF32 b when 0 <= b < 2^32 and fl_gamma I (b32_of_bits b);
   FlA64 I contains VF64 b likewise with 2^64; FlOther contains every value *)
Definition fl_any_top : top fl_any_lattice.                (* FlOther *)
Definition fl_any_widening_rank : bounded_widening_rank fl_any_lattice.
(* wrank FlBot = 8; wrank (FlA32 I) = 1 + the rank of I, likewise FlA64; wrank FlOther = 0;
   wbound = 8 *)
Definition float_ssa_domain : sparse_domain fl_any cval sop.
(* fact_lat = fl_any_lattice, fact_conc = fl_any_concretisation, top_fact = FlOther;
   op_abs (OExt tag) [FlA32 I; FlA32 J] = FlA32 (fl_bin o' I J) when float_ext_decode tag =
   Some (F32, FArith o'), likewise FlA64 for F64; every other operator or fact gives FlOther;
   assume_value _ a = a; assume_args (OExt tag) true [FlA32 I; FlA32 J] = [FlA32 I'; FlA32 J']
   with (I', J') = fl_assume_lt I J when float_ext_decode tag = Some (F32, FLt), likewise for F64,
   and assume_args _ _ fs = fs otherwise *)
Definition float_problem (nm32 : @nan_model 24 128) (nm64 : @nan_model 53 1024)
    (P : program) (f : func) (vals : list vid) (entry : vid -> fl_any) :
  sparse_problem astate event label ssa_edge vid sop cval fl_any :=
  SparseProblem (ssa_block_view (float_ext nm32 nm64) P f) float_ssa_domain vals entry.

Definition nan_domain_ssa : demand_domain nan_demand (option cval).
(* dlat as in nan_domain; dagree NotDemanded u v is True, including for None and Some. For a
   demanded value, Some u and Some v agree by nan_agree on decoded floats when both are VF32 in
   range or both VF64 in range, and by u = v otherwise; any case involving None agrees exactly
   when the option values are equal. Integers, pointers and functions agree exactly, and a float
   and a non-float never agree. Demanded true true agreement entails equality of the option values,
   including out-of-range float bit patterns. *)
Definition ssa_nan_demand_view (ext : nat -> list cval -> option cval) (P : program) (f : func) :
  demand_view astate event (label * nat) ssa_edge vid (option cval) nan_demand.
(* dgraph, ddefs and dlookup are those of ssa_demand_view ext P f.
   dnec e: every operand that ssa_demand_view marks needed at e (the operands of an output, a
   branch, a switch, a call, a return, a store, a free and a possibly trapping instruction), with
   the demand Demanded true true, since their bit patterns are observable or steer control; and
   the operands of an IOp with OExt, which may trap on the shape of its operands, with
   Demanded false false. dexit n is the raw ssa_demand_view's exit operands, each with
   Demanded true true, preserving their order and duplicates.
   dback e x NotDemanded = nil. For a demanded result and def x = Op o args in
   ssa_block_view ext P f:
   for o = OExt tag with float_ext_decode tag = Some (_, b) and args = [a1; a2], the pairs
   (a1, d1) and (a2, d2) with (d1, d2) = nan_back b d; for every other operator,
   the arguments with Demanded true true. For a Param definition and demand d = Demanded sg pl,
   map each pair (y, _) in dback (ssa_demand_view ext P f) e x true to (y, d), preserving
   its order and duplicates. For an Arbitrary definition, return nothing.
   Omitting bottom pairs preserves their semantic demand contribution and establishes d_back_bot;
   the separate dnec demands retain OExt trap-shape observations. Prove d_vars for every node,
   including unreachable blocks, and use full-demand option equality for d_exits. *)
```

## Theorems

```coq
(** The interval lattice satisfies the lattice laws, and its concretisation is monotone. *)
Theorem fl_lattice_laws :
  lattice_laws fl_lattice /\ concretisation_laws fl_lattice fl_concretisation.
(** Every float is in the top element, and nothing is in the bottom. *)
Theorem fl_top_sound (x : fl) : fl_gamma fl_top x.
Theorem fl_bot_empty (x : fl) : ~ fl_gamma (bot fl_lattice) x.
(** The subnormal threshold is the smallest normal number, so the predicate is neither empty nor
    everything: the smallest positive float is subnormal, and one is not. *)
Theorem subnormal_proper (Hp : (2 <= prec)%Z) :
  (exists x : fl, subnormal x) /\ (exists y : fl, B2R prec emax y = 1%R /\ ~ subnormal y).
```
Proof idea: unfold `fl_gamma` by the shape of `B2FF`; the order on bounds is `Bcompare`, which is
a total preorder on non-NaN floats (Flocq's `Bcompare_correct`); the interval lattice's laws are
case analyses on the flags and on the ordering of the bounds, an empty interval being below
everything. The smallest positive float is `B754_finite false 1 emin`, of magnitude
`2^(3 - emax - prec)`, which is below `2^(2 - emax)` because `prec >= 2`; the float `1` has
magnitude
at least `2^(2 - emax)` because `emax > prec >= 2`. Card: FLT-1.

```coq
(** Each abstract operator contains the float result, for every NaN model. *)
Theorem fl_bin_sound (nm : nan_model) (o : farith) (I J : fl_interval) (x y : fl) :
  fl_gamma I x -> fl_gamma J y -> fl_gamma (fl_bin o I J) (fl_eval_bin nm o x y).
Theorem fl_neg_sound (nm : nan_model) (I : fl_interval) (x : fl) :
  fl_gamma I x -> fl_gamma (fl_neg I) (fl_eval_neg nm x).
Theorem fl_abs_sound (nm : nan_model) (I : fl_interval) (x : fl) :
  fl_gamma I x -> fl_gamma (fl_abs I) (fl_eval_abs nm x).
(** Comparison refinement keeps both operands that satisfy the comparison. *)
Theorem fl_assume_lt_sound (I J : fl_interval) (x y : fl) :
  fl_gamma I x -> fl_gamma J y -> Bcompare prec emax x y = Some Lt ->
  fl_gamma (fst (fl_assume_lt I J)) x /\ fl_gamma (snd (fl_assume_lt I J)) y.
```
Proof idea: Flocq's correctness of the operators (`Bplus_correct` and its siblings) gives the exact
rounded real result of finite operands, with the overflow and special cases as separate lemmas;
monotonicity of rounding bounds the result between the directed roundings of the exact bounds; the
flags handle NaN (an operand NaN, or an invalid operation, whatever `nan_choice` returns), zero
signs, underflow and subnormals. Negation and absolute value are exact except on NaN, where the
flag covers the model's answer. `Bcompare x y = Some Lt` excludes NaN operands. Card: FLT-1.

```coq
(** The demand lattice satisfies the lattice laws. *)
Theorem nan_lattice_laws : lattice_laws (dlat nan_domain).
(** NaN agreement is an agreement: reflexive, antitone in the demand, symmetric, and trivial at
    NotDemanded. *)
Theorem nan_domain_laws :
  agreement_laws (dlat nan_domain) (dagree nan_domain) /\
  agreement_symmetric (dagree nan_domain) /\
  (forall u v, agree (dagree nan_domain) (bot (dlat nan_domain)) u v).
(** NaN observability is sound for the arithmetic operators: if the operands agree on the demands
    that `nan_back` computes, the results agree on the demand on the result. *)
Theorem nan_back_sound (nm : nan_model) (o : farith) (d : nan_demand) (x y x' y' : fl) :
  nan_agree (fst (nan_back (FArith o) d)) x x' -> nan_agree (snd (nan_back (FArith o) d)) y y' ->
  nan_agree d (fl_eval_bin nm o x y) (fl_eval_bin nm o x' y').
(** A comparison sees whether an operand is NaN and nothing else about it. *)
Theorem fl_lt_agrees (x y x' y' : fl) :
  nan_agree (Demanded false false) x x' -> nan_agree (Demanded false false) y y' ->
  fl_lt x y = fl_lt x' y'.
```
Proof idea: `nan_lattice_laws` and `nan_domain_laws` by cases on the five demands and the shape of
`B2FF`. For `nan_back_sound`: a demand of the sign or the payload makes both operands agree fully,
so non-NaN operands are equal (`B2FF` is injective up to proof irrelevance) and NaN operands have
the same sign and payload, and `nan_choice_local` makes the choice, and so the result, identical,
the NaN produced from non-NaN operands (inf - inf) included; the demand `Demanded false false`
needs only that NaN-ness and the non-NaN values agree, from which the NaN-ness of the result and,
when it is not NaN, the result follow. For `fl_lt_agrees`, `Bcompare` is `None` when an operand is
NaN and depends only on the values otherwise. Card: FLT-1.

```coq
Section FloatSsaTheorems.
Context (nm32 : @nan_model 24 128) (nm64 : @nan_model 53 1024).
Local Notation fx := (float_ext nm32 nm64).

Theorem float_ext_respects (P : program) :
  ext_sigs P = float_ext_sigs -> ext_respects fx P.
(** The result type follows by decoding each tag and inspecting its operands. Card: FLT-1. *)

(** The operator numbering is injective: decoding inverts the tag, and a tag that decodes is the
    tag of what it decodes to. *)
Theorem float_ext_tag_decode (w : fw) (o : fbop) :
  float_ext_decode (float_ext_tag w o) = Some (w, o).
Theorem float_ext_decode_tag (tag : nat) (w : fw) (o : fbop) :
  float_ext_decode tag = Some (w, o) -> float_ext_tag w o = tag.
(** The Ssa NaN agreement is a lattice with an agreement, like the one on floats. *)
Theorem nan_domain_ssa_laws :
  lattice_laws (dlat nan_domain_ssa) /\
  agreement_laws (dlat nan_domain_ssa) (dagree nan_domain_ssa) /\
  agreement_symmetric (dagree nan_domain_ssa) /\
  (forall u v, agree (dagree nan_domain_ssa) (bot (dlat nan_domain_ssa)) u v).
(** The float value domain has the laws that VIEW-4 needs, for every truth function that reads a
    nonzero integer as true. *)
Theorem float_ssa_domain_laws (truth : cval -> bool) :
  (forall w z, truth (VInt w z) = negb (Z.eqb z 0)) ->
  sparse_domain_laws float_ssa_domain truth (op_eval fx).
```
Proof idea: the numbering is a case analysis on `w` and the five operators. `nan_domain_ssa_laws` is
`nan_lattice_laws` and `nan_domain_laws` read through the decoding, with exact equality outside
floats. For `float_ssa_domain_laws`: `fl_lattice_laws` and the lattice of facts give
`dom_lattice` and `dom_conc`; `fact_bot_empty` and `top_sound` are the cases `FlBot` and `FlOther`;
`op_sound` is `fl_bin_sound` composed with the round trip of `b32_of_bits` and `bits_of_b32`
(`bits_of_binary_float_of_bits` on an in-range pattern, and `fx` returns in-range patterns);
`assume_args_sound` for `FLt` and `true` is `fl_assume_lt_sound`, the result `VInt W32 1` meaning
that `fl_lt` holds, and every other case is the identity. Card: FLT-1.

```coq
(** Float value analysis is sound on Ssa: every float value defined in a reachable activation
    lies in the interval of its fact. *)
Theorem ssa_float_value_sound (P : program) (f : func) (vals : list vid) (entry : vid -> fl_any)
    (sigma : sparse_unknown label ssa_edge vid -> lift_bot fl_any) :
  wf_program P ->
  (forall s x c, reachable_state (activation fx P f) s ->
     val (ssa_block_view fx P f) s x = Some c -> In x vals) ->
  (forall s x c, initial (activation fx P f) s -> val (ssa_block_view fx P f) s x = Some c ->
     exists b i, def (ssa_block_view fx P f) x = Param b i /\
       In b (Graph.entries (cfg (base (ssa_block_view fx P f)))) /\
       gamma fl_any_concretisation (entry x) c) ->
  post_solution (lift_bot_lattice fl_any_lattice)
    (sparse_system label_encoding var_encoding (float_problem nm32 nm64 P f vals entry)) sigma ->
  forall s x c, reachable_state (activation fx P f) s ->
    val (ssa_block_view fx P f) s x = Some c ->
    gamma (lift_bot_gamma fl_any_concretisation) (sigma (UVal x)) c.
(** The NaN demand view of Ssa satisfies the laws of the demand framework. *)
Theorem ssa_nan_demand_view_laws (P : program) (f : func) :
  wf_program P ->
  demand_laws (activation fx P f) (activation_endings fx P f)
    (reachable_state (activation fx P f)) var_encoding nan_domain_ssa
    (ssa_nan_demand_view fx P f).
(** NaN observability on Ssa: two activation states that differ only in the payload and sign of
    NaNs that nothing observes behave the same. *)
Theorem ssa_nan_demand_sound (P : program) (f : func)
    (sigma : (label * nat) ->
      finite_map var_encoding (dvars (ssa_nan_demand_view fx P f)) nan_demand) (s0 t0 : astate) :
  wf_program P ->
  post_solution (demand_lattice var_encoding nan_domain_ssa (ssa_nan_demand_view fx P f))
    (demand_system var_encoding nan_domain_ssa (ssa_nan_demand_view fx P f)) sigma ->
  initial (activation fx P f) s0 -> initial (activation fx P f) t0 ->
  point (dgraph (ssa_nan_demand_view fx P f)) t0 = point (dgraph (ssa_nan_demand_view fx P f)) s0 ->
  agree (demand_agreement var_encoding nan_domain_ssa (ssa_nan_demand_view fx P f))
    (sigma (point (dgraph (ssa_nan_demand_view fx P f)) s0)) s0 t0 ->
  same_behaviour (activation fx P f) (activation_endings fx P f) s0
    (activation fx P f) (activation_endings fx P f) t0.
End FloatSsaTheorems.
```
Proof idea: the first is `sparse_sound` for `float_problem`, with `ssa_block_view_laws` from EX-5a,
`float_ssa_domain_laws` (the view's `truth` is `ssa_truth_nonzero`) and `fl_bin_sound` inside; the
second checks the laws of the demand framework for the toy as for neededness, the per-operator
step being `nan_back_sound` for the float operators and `fl_lt_agrees` for the comparison, the
trap shape being fixed by the demand `Demanded false false` on the operands of `OExt`, and the rest
being exact; the third is `demand_sound` with `ssa_nan_demand_view_laws` and `reachable_invariant`.
Card: FLT-1.

## Algorithms and references

- IEEE 754-2019 for the operations and for the NaN payload and sign model; Flocq 4 (Boldo and
  Melquiond, "Flocq: a unified library for proving floating-point algorithms in Coq", 2011) for
  `binary_float`, `Bcompare`, `Bplus`, `B2FF`, the bit conversions `b32_of_bits` and `bits_of_b32`
  and the correctness lemmas of the operators. The NaN choice is the argument that Flocq's
  operations take for exactly this purpose; `nan_choice_local` is the one property that real
  hardware satisfies and the analysis needs.
- Float intervals with explicit NaN and signed-zero flags follow the treatment of floating-point in
  abstract interpreters (Miné, "Relational abstract domains for the detection of floating-point
  run-time errors", 2004); the NaN-observability demand is the shape of demanded bits with one
  bit pattern per NaN. The widening that sends a moving bound to infinity is that of the classical
  interval domain (Cousot and Cousot, 1977).

## Performance notes

- Every abstract operator is a constant number of Flocq operations on `binary_float` values, with
  directed rounding for the bounds; nothing loops over a list, and joins, widenings and
  comparisons are O(1).
- A bound is a sigma value `{x | is_nan x = false}`; the proof is erased by extraction, so a bound
  is the float itself. A fact of `fl_any` holds at most two bounds and four flags.
- `float_ext` decodes and encodes bit patterns with `b32_of_bits` and `bits_of_b32`, O(1) in the
  width, and the tag numbering is arithmetic.
- `fl_widening_rank` and `fl_any_widening_rank` have bounds 6 and 8, so `solve_total` with
  widening needs no fuel; the NaN demand is a five-point lattice of height 3 and `nan_agree` is
  O(1).

## Open questions

1. **Flocq conventions.** The arity of Flocq's operators (which of `prec`, `emax` and the proofs
   `Prec_gt_0` and `Prec_lt_emax` are explicit, and the shape of the NaN-choice argument) follows
   the
   installed Flocq 4.2.2; the card adapts the signatures, not the statements.
2. **Axiom names.** The list in the conventions is the exact allowance for the pinned Flocq
   dependencies; a theorem that depends on fewer is fine. `Print Assumptions` checks actual
   theorem dependencies against it.
3. **Operators not covered.** Conversions between integers and floats, `sqrt`, fused multiply-add
   and `min` and `max` have no operator or theorem here; a client that needs them extends `fbop`
   and every theorem that cases on it.

## Requests to other documents

1. **Examples (EX-5a).** `ssa_truth_nonzero`:
   `forall ext P f w z, truth (ssa_block_view ext P f) (VInt w z) = negb (Z.eqb z 0)`. Why:
   `float_ssa_domain_laws` needs the view's `truth` to read a nonzero integer as true, and
   `ssa_float_value_sound` instantiates it.

<!-- AUD-API-NUM-BEGIN -->

# NUM source contracts

Definitions specify source work; future theorem types are proof obligations.

## Galois.Float.FloatAuditDiv

Card: AUD-FL

Source destination: `theories/Float/FloatAuditDiv.v`.

```rocq
(** * Floating division statement checks

    This scratch file checks future division and signed-zero proposition types.
    For example, zero's sign is observed through its floating representation.
    Builds on: FloatInterval and FloatOps. *)

From Stdlib Require Import ZArith Reals.
From Flocq Require Import Core IEEE754.BinarySingleNaN IEEE754.Binary IEEE754.Bits.
From Galois.Float Require Import FloatInterval FloatOps.
From Galois.Float Require Import FloatAuditDivPlain.
From Galois.Float Require Import FloatAuditDivEndpoint.

(** * Prospective soundness types *)

Section FloatStatements.
  Context {prec emax : Z} {Hprec : Prec_gt_0 prec} {Hmax : Prec_lt_emax prec emax}.
  Local Abbreviation fl := (binary_float prec emax).
  (** The public division body uses the fixed format endpoints and constructs no audit trace. *)
  Definition float_div_split (I J : @fl_interval prec emax) : @fl_interval prec emax :=
    audit_float_split_candidate audit_float_positive_endpoint audit_float_negative_endpoint I J.

  (** Every concrete division result belongs to the selected interval. *)
  Definition split_sound_type : Prop :=
    forall (nm : @nan_model prec emax) (I J : @fl_interval prec emax) (x y : fl),
      fl_gamma I x -> fl_gamma J y -> fl_gamma (float_div_split I J) (fl_eval_bin nm FDiv x y).

  (** A represented zero has its actual sign flag set. *)
  Definition zero_sign_sound_type : Prop :=
    forall (nm : @nan_model prec emax) (I J : @fl_interval prec emax) (x y : fl) (s : bool),
      fl_gamma I x -> fl_gamma J y ->
      B2FF prec emax (fl_eval_bin nm FDiv x y) = F754_zero s ->
      (if s then may_neg_zero (float_div_split I J) else may_pos_zero (float_div_split I J)) = true.

  (** The optional selector retains the original transfer when disabled. *)
  Definition float_bin_select (use_split : bool) (o : farith) (I J : @fl_interval prec emax)
      : @fl_interval prec emax :=
    match use_split, o with
    | true, FDiv => float_div_split I J
    | _, _ => fl_bin o I J
    end.

  (** Every selected operation is sound for the existing evaluation semantics. *)
  Definition select_sound_type : Prop :=
    forall use_split (nm : @nan_model prec emax) o (I J : @fl_interval prec emax) (x y : fl),
      fl_gamma I x -> fl_gamma J y ->
      fl_gamma (float_bin_select use_split o I J) (fl_eval_bin nm o x y).
End FloatStatements.

(** Exact retained public semantic spellings and both selector branches. *)
Definition float_div_split_sound_type := @split_sound_type.
Definition float_zero_sign_sound_type := @zero_sign_sound_type.
Definition float_bin_select_sound_type := @select_sound_type.
Section ExactSelectors.
 Context {prec emax : Z} {Hprec : Prec_gt_0 prec} {Hmax : Prec_lt_emax prec emax}.

 Definition float_bin_select_legacy_type : Prop := forall o I J,
   @float_bin_select prec emax Hprec Hmax false o I J = fl_bin o I J.
 Definition float_bin_select_split_type : Prop := forall I J,
   @float_bin_select prec emax Hprec Hmax true FDiv I J = float_div_split I J.
End ExactSelectors.
```

## Galois.Float.FloatAuditDivBody

Card: AUD-FL-BODY

Source destination: `theories/Float/FloatAuditDivBody.v`.

```rocq
(** * Operand-retaining Float primitive body equations

    This file fixes finite division, rounding and every numeric one-bit alignment invocation.
    For example, a positive alignment amount executes that many successive shift-record steps.
    Builds on: Rocq SpecFloat, pinned Flocq rounding helpers and the shared fixed weights. *)

From Stdlib Require Import List NArith PArith ZArith Bool Floats.SpecFloat.
From Flocq Require Import Calc.Round IEEE754.BinarySingleNaN.
From Galois.Collections Require Import CollectionsAuditCost.
Import List.ListNotations.

Inductive float_body_event : Type :=
  | FloatBodyCase (site : nat)
  | FloatBodyBuild (site : nat)
  | FloatBodyAdd (a b : Z)
  | FloatBodySub (a b : Z)
  | FloatBodyCompare (a b : Z)
  | FloatBodyDivide (a b : Z)
  | FloatBodyMultiply (a b : Z)
  | FloatBodyParity (value : Z)
  | FloatBodyShift (value amount : Z)
  | FloatBodyPower (base exponent : Z)
  | FloatBodyConvert (value : Z)
  | FloatBodyDigits (value : Z)
  | FloatBodyRoundChoice (rounding : mode) (negative : bool) (value : Z) (loc : location)
  | FloatBodyShiftOne (before after : shr_record).

(** Binary iterator equations retain each actual before/after record and binary-fuel case. *)
Fixpoint float_body_shift_iter (fuel : positive) (input : shr_record)
    : shr_record * list float_body_event :=
  match fuel with
  | xH =>
    let out := shr_1 input in
    (out, [FloatBodyCase 0; FloatBodyShiftOne input out])
  | xO p =>
    let '(mid, first) := float_body_shift_iter p input in
    let '(out, second) := float_body_shift_iter p mid in
    (out, FloatBodyCase 0 :: first ++ second)
  | xI p =>
    let initial := shr_1 input in
    let '(mid, first) := float_body_shift_iter p initial in
    let '(out, second) := float_body_shift_iter p mid in
    (out, [FloatBodyCase 0; FloatBodyShiftOne input initial] ++ first ++ second)
  end.

Definition float_body_exponent (prec emax value : Z) : Z * list float_body_event :=
  let precise := (value - prec)%Z in
  let minimum := emin prec emax in
  (fexp prec emax value,
    [FloatBodySub value prec; FloatBodySub 3 emax; FloatBodySub (3 - emax)%Z prec;
      FloatBodyCompare precise minimum]).

(** Alignment retains its actual numeric amount and every completed shift invocation. *)
Definition float_body_align (prec emax mantissa exponent : Z) (loc : location)
    : (shr_record * Z) * list float_body_event :=
  let record := shr_record_of_loc mantissa loc in
  let digits := Zdigits2 mantissa in
  let magnitude := (digits + exponent)%Z in
  let '(target, exponent_events) := float_body_exponent prec emax magnitude in
  let amount := (target - exponent)%Z in
  let prefix := [FloatBodyCase 1; FloatBodyBuild 2; FloatBodyDigits mantissa;
    FloatBodyAdd digits exponent] ++ exponent_events ++ [FloatBodySub target exponent;
      FloatBodyCase 3] in
  match amount with
  | Zpos p =>
    let '(out, shifts) := float_body_shift_iter p record in
    ((out, (exponent + amount)%Z), prefix ++ shifts ++
      [FloatBodyAdd exponent amount; FloatBodyBuild 4])
  | _ => ((record, exponent), prefix ++ [FloatBodyBuild 4])
  end.

Definition float_body_choice (rounding : mode) (negative : bool) (mantissa : Z) (loc : location)
    : Z * list float_body_event :=
  let increment := match rounding with
    | mode_NE => round_N (negb (Z.even mantissa)) loc
    | mode_ZR => false
    | mode_DN => round_sign_DN negative loc
    | mode_UP => round_sign_UP negative loc
    | mode_NA => round_N true loc
    end in
  let prefix := [FloatBodyRoundChoice rounding negative mantissa loc; FloatBodyCase 5] in
  if increment then ((mantissa + 1)%Z, prefix ++ [FloatBodyAdd mantissa 1])
  else (mantissa, prefix).

Definition float_body_fit (prec emax : Z) (rounding : mode) (negative : bool)
    (mantissa : positive) (exponent : Z) : spec_float * list float_body_event :=
  let limit := (emax - prec)%Z in
  let prefix := [FloatBodySub emax prec; FloatBodyCompare exponent limit; FloatBodyCase 6] in
  if (exponent <=? limit)%Z then
    (S754_finite negative mantissa exponent, prefix ++ [FloatBodyBuild 7]) else
  let infinite := overflow_to_inf rounding negative in
  if infinite then
    (S754_infinity negative, prefix ++ [FloatBodyCase 8; FloatBodyCase 9; FloatBodyBuild 10])
  else
    let power := (2 ^ prec)%Z in
    let maximum := (power - 1)%Z in
    let final_exponent := (emax - prec)%Z in
    (S754_finite negative (Z.to_pos maximum) final_exponent,
      prefix ++ [FloatBodyCase 8; FloatBodyCase 9; FloatBodyPower 2 prec;
        FloatBodySub power 1; FloatBodyConvert maximum; FloatBodySub emax prec; FloatBodyBuild 7]).

(** Rounding performs both real alignments around its exact rounding choice. *)
Definition float_body_round (prec emax : Z) (rounding : mode) (negative : bool)
    (mantissa exponent : Z) (loc : location) : spec_float * list float_body_event :=
  let '((first, e1), first_trace) := float_body_align prec emax mantissa exponent loc in
  let first_mantissa := shr_m first in
  let first_loc := loc_of_shr_record first in
  let '(chosen, choice_trace) := float_body_choice rounding negative first_mantissa first_loc in
  let '((second, e2), second_trace) := float_body_align prec emax chosen e1 loc_Exact in
  let prefix := first_trace ++ [FloatBodyCase 11; FloatBodyCase 12] ++ choice_trace ++
    second_trace ++ [FloatBodyCase 13; FloatBodyCase 14] in
  match shr_m second with
  | Z0 => (S754_zero negative, prefix ++ [FloatBodyBuild 15])
  | Zpos p =>
    let '(out, fitted) := float_body_fit prec emax rounding negative p e2 in
    (out, prefix ++ fitted)
  | Zneg _ => (S754_nan, prefix ++ [FloatBodyBuild 16])
  end.

Definition float_body_location (divisor remainder : Z) : location * list float_body_event :=
  let even := Z.even divisor in
  let prefix := [FloatBodyParity divisor; FloatBodyCase 17;
    FloatBodyCompare remainder 0; FloatBodyCase 18] in
  if (remainder =? 0)%Z then (loc_Exact, prefix) else
  let twice := (2 * remainder)%Z in
  if even then
    (loc_Inexact (Z.compare twice divisor), prefix ++ [FloatBodyMultiply 2 remainder;
      FloatBodyCompare twice divisor])
  else
    let incremented := (twice + 1)%Z in
    (loc_Inexact (match Z.compare incremented divisor with Gt => Gt | _ => Lt end),
      prefix ++ [FloatBodyMultiply 2 remainder; FloatBodyAdd twice 1;
        FloatBodyCompare incremented divisor; FloatBodyCase 19]).

(** Finite-core equations retain the actual scaling shift, dividend, divisor and location. *)
Definition float_body_core (prec emax m1 e1 m2 e2 : Z)
    : (Z * Z * location) * list float_body_event :=
  let d1 := Zdigits2 m1 in
  let d2 := Zdigits2 m2 in
  let lhs := (d1 + e1)%Z in
  let rhs := (d2 + e2)%Z in
  let input := (lhs - rhs)%Z in
  let '(desired, exponent_trace) := float_body_exponent prec emax input in
  let difference := (e1 - e2)%Z in
  let target := Z.min desired difference in
  let amount := (difference - target)%Z in
  let '(dividend, shifted) := match amount with
    | Z0 => (m1, [])
    | Zpos _ => (Z.shiftl m1 amount, [FloatBodyShift m1 amount])
    | Zneg _ => (0%Z, [])
    end in
  let '(quotient, remainder) := Z.div_eucl dividend m2 in
  let '(loc, location_trace) := float_body_location m2 remainder in
  ((quotient, target, loc), [FloatBodyDigits m1; FloatBodyDigits m2;
    FloatBodyAdd d1 e1; FloatBodyAdd d2 e2; FloatBodySub lhs rhs] ++ exponent_trace ++
    [FloatBodySub e1 e2; FloatBodyCompare desired difference; FloatBodySub difference target;
      FloatBodyCase 20] ++ shifted ++ [FloatBodyDivide dividend m2; FloatBodyCase 21] ++
 location_trace).

(** All numeric leaf charges are fixed and positive on their actual operands. *)
Definition float_body_event_work (event : float_body_event) : nat :=
  match event with
  | FloatBodyAdd a b | FloatBodySub a b | FloatBodyCompare a b => audit_binary_weight a b
  | FloatBodyDivide a b => audit_divide_weight a b
  | FloatBodyMultiply a b => audit_multiply_weight a b
  | FloatBodyParity value => S (audit_z_bits value)
  | FloatBodyShift value amount => audit_shift_weight value amount
  | FloatBodyPower base exponent =>
    (1 + audit_z_bits base * S (Z.to_nat (Z.max 0 exponent)))%nat
  | FloatBodyConvert value | FloatBodyDigits value => S (audit_z_bits value)
  | FloatBodyRoundChoice rounding _ value loc =>
    ((match rounding with mode_NE => S (audit_z_bits value) | _ => 1%nat end) +
      (match loc with loc_Exact => 1%nat | _ => 2%nat end) + 2)%nat
  | FloatBodyShiftOne input _ =>
    (6 + match shr_m input with Z0 => 0%nat | Zpos _ | Zneg _ => 1%nat end)%nat
  | _ => 1%nat
  end.

Definition float_body_work (events : list float_body_event) : nat :=
  fold_right (fun event total => (float_body_event_work event + total)%nat) 0%nat events.

(** Finite source correspondence retains exact finite-core output before rounding. *)
Definition float_body_core_erases_type : Prop := forall prec emax m1 e1 m2 e2,
  fst (float_body_core prec emax m1 e1 m2 e2) = SFdiv_core_binary prec emax m1 e1 m2 e2.

(** Both alignment and rounding bodies erase to the pinned numeric helpers. *)
Definition float_body_round_erases_type : Prop := forall prec emax rounding negative m e loc,
  fst (float_body_round prec emax rounding negative m e loc) =
    binary_round_aux prec emax rounding negative m e loc.

(** The actual positive shift amount is the exact number of recorded one-bit calls. *)
Definition float_body_shift_count_type : Prop := forall fuel input,
  length (filter (fun event =>
    match event with FloatBodyShiftOne _ _ => true | _ => false end)
      (snd (float_body_shift_iter fuel input))) = Pos.to_nat fuel.

(** This operand-size envelope prices arbitrary numeric shift lengths independently of bit length.
  *)
Definition float_body_shift_bound_type : Prop := forall fuel input,
  (float_body_work (snd (float_body_shift_iter fuel input)) <= 10 * Pos.to_nat fuel)%nat.
```

## Galois.Float.FloatAuditDivEndpoint

Card: AUD-FL

Source destination: `theories/Float/FloatAuditDivEndpoint.v`.

```rocq
(** * Least positive format value proposal.

    These scratch declarations state the endpoint property needed for splitting.
    For example, binary32 uses the exponent [-149].
    Builds on: Flocq Binary and FloatInterval. *)

From Stdlib Require Import ZArith Reals.
From Flocq Require Import Core IEEE754.BinarySingleNaN IEEE754.Binary IEEE754.Bits.
From Galois.Float Require Import FloatInterval FloatOps.

Section Endpoint.
Context {prec emax : Z} {Hprec : Prec_gt_0 prec} {Hmax : Prec_lt_emax prec emax}.
Local Abbreviation fl := (binary_float prec emax).

Definition audit_float_min_subnormal : fl :=
  @B754_finite prec emax false 1 (SpecFloat.emin prec emax)
    (Bulp_correct_aux prec emax Hprec Hmax).

Definition audit_float_positive_endpoint : @fl_finite_bound prec emax :=
  exist _ audit_float_min_subnormal eq_refl.

Definition audit_float_negative_endpoint : @fl_finite_bound prec emax :=
  exist _ (@B754_finite prec emax true 1 (SpecFloat.emin prec emax)
    (Bulp_correct_aux prec emax Hprec Hmax)) eq_refl.

(** The endpoint is the smallest positive finite nonzero value. *)
Definition audit_float_min_subnormal_correct_statement : Prop :=
  is_finite prec emax audit_float_min_subnormal = true /\
  (B2R prec emax audit_float_min_subnormal = bpow radix2 (3 - emax - prec))%R /\
  forall x : fl, is_finite prec emax x = true -> (0 < B2R prec emax x)%R ->
    (B2R prec emax audit_float_min_subnormal <= B2R prec emax x)%R.
End Endpoint.
```

## Galois.Float.FloatAuditDivPlain

Card: AUD-FL

Source destination: `theories/Float/FloatAuditDivPlain.v`.

```rocq
(** * Sign-separated finite division pilot.

    This scratch computation splits a finite divisor around zero.
    For example, a positive divisor piece uses a positive nonzero endpoint.
    Builds on: FloatOps and Flocq Binary. *)

From Stdlib Require Import ZArith Reals Bool NArith.
From Flocq Require Import Core IEEE754.BinarySingleNaN IEEE754.Binary IEEE754.Bits.
From Galois.Float Require Import FloatInterval FloatOps.

Section Split.
Context {prec emax : Z} {Hprec : Prec_gt_0 prec} {Hmax : Prec_lt_emax prec emax}.
Local Abbreviation fl := (binary_float prec emax).

Variable positive_min negative_max : @fl_finite_bound prec emax.

(** The endpoints surround every representable finite nonzero divisor. *)
Definition audit_float_endpoint_laws : Prop :=
  (0 < B2R prec emax (proj1_sig positive_min))%R /\
  (B2R prec emax (proj1_sig negative_max) < 0)%R /\
  (forall x : fl, is_finite prec emax x = true -> (0 < B2R prec emax x)%R ->
    (B2R prec emax (proj1_sig positive_min) <= B2R prec emax x)%R) /\
  (forall x : fl, is_finite prec emax x = true -> (B2R prec emax x < 0)%R ->
    (B2R prec emax x <= B2R prec emax (proj1_sig negative_max))%R).

Definition audit_float_finite_max (a b : @fl_finite_bound prec emax)
    : @fl_finite_bound prec emax :=
  if nn_le (fl_finite_nn a) (fl_finite_nn b) then b else a.

Definition audit_float_finite_min (a b : @fl_finite_bound prec emax)
    : @fl_finite_bound prec emax :=
  if nn_le (fl_finite_nn a) (fl_finite_nn b) then a else b.

Definition audit_float_piece (a b c d : @fl_finite_bound prec emax)
    : @fl_interval prec emax :=
  if nn_le (fl_finite_nn c) (fl_finite_nn d) then
    fl_bounds_interval
      (fl_lower_corners FDiv (proj1_sig a) (proj1_sig b) (proj1_sig c) (proj1_sig d))
      (fl_upper_corners FDiv (proj1_sig a) (proj1_sig b) (proj1_sig c) (proj1_sig d))
  else fl_bottom.

Definition audit_float_zero_masks (I J : @fl_interval prec emax) : bool * bool :=
  let nneg := may_neg_zero I || fl_has_class I (FlFinite true) in
  let npos := may_pos_zero I || fl_has_class I (FlFinite false) in
  let dneg := fl_has_class J (FlFinite true) in
  let dpos := fl_has_class J (FlFinite false) in
  ((nneg && dpos) || (npos && dneg), (nneg && dneg) || (npos && dpos)).

Definition audit_float_set_zero_masks (I J raw : @fl_interval prec emax)
    : @fl_interval prec emax :=
  let '(negative, positive) := audit_float_zero_masks I J in
  FlInterval (flo raw) (fhi raw) (may_nan raw) (may_neg_zero raw && negative)
    (may_pos_zero raw && positive) (may_subnormal raw).

(** The outer candidate preserves the existing exceptional-class result. *)
Definition audit_float_split_candidate (I J : @fl_interval prec emax)
    : @fl_interval prec emax :=
  let finite :=
    match fl_finite_bounds I, fl_finite_bounds J with
    | Some (a,b), Some (c,d) =>
      let neg := audit_float_piece a b c (audit_float_finite_min d negative_max) in
      let pos := audit_float_piece a b (audit_float_finite_max c positive_min) d in
      audit_float_set_zero_masks I J (fl_join neg pos)
    | _, _ => fl_bottom
    end in
  fl_join finite (fl_special_bin FDiv I J).

(** Every observed result is retained when the endpoints satisfy their laws. *)
Definition audit_float_split_candidate_sound_statement : Prop :=
  audit_float_endpoint_laws ->
  forall (nm : @nan_model prec emax) I J (x y : fl),
    fl_gamma I x -> fl_gamma J y ->
    fl_gamma (audit_float_split_candidate I J) (fl_eval_bin nm FDiv x y).
End Split.
```

## Galois.Float.FloatAuditDivPrecision

Card: AUD-FL

Source destination: `theories/Float/FloatAuditDivPrecision.v`.

```rocq
(** * Floating precision statement check

    This scratch file elaborates the binary32 signed-zero precision statement.
    For example, positive zero divided by one retains its positive sign.
    Builds on: FloatInterval and FloatOps. *)

From Stdlib Require Import ZArith Reals.
From Flocq Require Import Core IEEE754.BinarySingleNaN IEEE754.Binary IEEE754.Bits.
From Galois.Float Require Import FloatInterval FloatOps.
From Galois.Float Require Import FloatAuditDiv.

(** * Concrete witnesses and proposition type *)

Definition audit_bound32 (negative : bool) (mantissa : positive) (exponent : Z)
    (Hb : SpecFloat.bounded 24 128 mantissa exponent = true) : @fl_nn 24 128 :=
  exist _ (@Binary.B754_finite 24 128 negative mantissa exponent Hb) eq_refl.
Definition audit_zero32 (negative : bool) : @fl_nn 24 128 :=
  exist _ (@Binary.B754_zero 24 128 negative) eq_refl.
Definition audit_inf32 (negative : bool) : @fl_nn 24 128 :=
  exist _ (@Binary.B754_infinity 24 128 negative) eq_refl.
Definition audit_one32 := audit_bound32 false 8388608 (-23) eq_refl.
Definition audit_two32 := audit_bound32 false 8388608 (-22) eq_refl.
Definition audit_minus_one32 := audit_bound32 true 8388608 (-23) eq_refl.
Definition audit_point_one32 : @fl_interval 24 128 :=
  FlInterval audit_one32 audit_one32 false false false true.
Definition audit_zero_to_two32 : @fl_interval 24 128 :=
  FlInterval (audit_zero32 false) audit_two32 false false true true.
Definition audit_positive_zero_only32 : @fl_interval 24 128 :=
  FlInterval (audit_inf32 false) (audit_inf32 true) false false true false.

Section FutureSplit32.
  Context {Hprec32 : Prec_gt_0 24} {Hmax32 : Prec_lt_emax 24 128}.

Definition float_div_split_precision_type : Prop :=
  fl_gamma (fl_bin FDiv audit_point_one32 audit_zero_to_two32) (proj1_sig audit_minus_one32) /\
  ~ fl_gamma (float_div_split audit_point_one32 audit_zero_to_two32)
      (proj1_sig audit_minus_one32) /\
  fl_gamma (float_div_split audit_point_one32 audit_zero_to_two32)
    (proj1_sig (audit_inf32 false)) /\
  may_neg_zero (fl_bin FDiv audit_positive_zero_only32 audit_point_one32) = true /\
  may_neg_zero (float_div_split audit_positive_zero_only32 audit_point_one32) = false /\
  may_pos_zero (float_div_split audit_positive_zero_only32 audit_point_one32) = true.

End FutureSplit32.
```

## Galois.Float.FloatAuditDivSource

Card: AUD-FL

Source destination: `theories/Float/FloatAuditDivSource.v`.

```rocq
(** * Complete sign-split division source equations

    This file composes both sign pieces, strict exceptional tests, joins and zero masks.
    For example, every exceptional class pair checks both operand classes even after rejection.
    Builds on: FloatInterval, FloatOps, FLSplitPilot, FLMin and the audit weights. *)

From Stdlib Require Import List ZArith NArith Bool Floats.SpecFloat.
From Flocq Require Import Core IEEE754.BinarySingleNaN IEEE754.Binary IEEE754.Bits.
From Galois.Float Require Import FloatInterval FloatOps.
From Galois.Float Require Import FloatAuditDiv.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Float Require Import FloatAuditDivPlain.
From Galois.Float Require Import FloatAuditDivEndpoint.
From Galois.Float Require Import FloatAuditDivBody.
Import List.ListNotations.

Section FloatSource.
Context {prec emax : Z} {Hprec : Prec_gt_0 prec} {Hmax : Prec_lt_emax prec emax}.
Local Abbreviation fl := (binary_float prec emax).
Local Abbreviation nn := (@fl_nn prec emax).
Local Abbreviation finite := (@fl_finite_bound prec emax).
Local Abbreviation interval := (@fl_interval prec emax).

(** Flocq leaves retain exact formats, modes, operands and results; they are not client oracles. *)
Inductive float_source_event : Type :=
  | FloatCase (site : nat)
  | FloatConstruct (site : nat)
  | FloatProjection (site : nat)
  | FloatBoolean (site : nat) (lhs rhs : bool)
  | FloatCompare (lhs rhs : fl) (output : option comparison)
  | FloatDivide (rounding : mode) (lhs rhs : fl)
      (output : BinarySingleNaN.binary_float prec emax)
  | FloatFormatBound (normal maximum : bool)
  | FloatInteger (lhs rhs : Z)
  | FloatEndpoint (negative : bool).

Definition float_run (A : Type) : Type := A * list float_source_event.

Definition float_bind {A B} (first : float_run A) (next : A -> float_run B) : float_run B :=
  let '(a, first_trace) := first in
  let '(b, next_trace) := next a in (b, first_trace ++ next_trace).

Definition float_mark {A} (site : nat) (body : float_run A) : float_run A :=
  (fst body, FloatCase site :: snd body).

Definition float_nn_compare (x y : nn) : float_run bool :=
  let raw := Bcompare prec emax (proj1_sig x) (proj1_sig y) in
  (nn_le x y, [FloatProjection 0; FloatProjection 0;
    FloatCompare (proj1_sig x) (proj1_sig y) raw; FloatCase 1]).

Definition float_minmax (minimum : bool) (x y : nn) : float_run nn :=
  let '(ordered, compared) := float_nn_compare x y in
  (if ordered then (if minimum then x else y) else (if minimum then y else x),
    compared ++ [FloatCase 2]).

Definition float_active (I : interval) : float_run bool :=
  let '(out, compared) := float_nn_compare (flo I) (fhi I) in
  (out, [FloatProjection 3; FloatProjection 4] ++ compared).

Definition float_full_bound (lower : bool) (I : interval) : float_run nn :=
  let has_zero := fl_has_zero I in
  let prefix := [FloatProjection 5; FloatProjection 6;
    FloatBoolean 7 (may_neg_zero I) (may_pos_zero I); FloatCase 8] in
  if has_zero then
    let '(active, active_trace) := float_active I in
    if active then
      let bound := if lower then flo I else fhi I in
      let '(out, compared) := float_minmax lower bound fl_zero in
      (out, prefix ++ active_trace ++ [FloatCase 9; FloatProjection 10;
        FloatConstruct 11; FloatConstruct 12] ++ compared)
    else (fl_zero, prefix ++ active_trace ++ [FloatCase 9; FloatConstruct 11; FloatConstruct 12])
  else (if lower then flo I else fhi I, prefix ++ [FloatProjection 10]).

Definition float_clamp (x : nn) : float_run finite :=
  let extra := match proj1_sig x with
    | @B754_infinity _ _ negative =>
      [FloatCase 13; FloatFormatBound false true] ++
        if negative then [FloatCase 14; FloatBoolean 15 negative false; FloatConstruct 16] else []
    | _ => []
    end in
  (nn_finite_clamp x, [FloatCase 17; FloatCase 18] ++ extra ++
    [FloatConstruct 19; FloatConstruct 20]).

(** Both infinity tag checks execute even when the bound comparison has already failed. *)
Definition float_bounds (I : interval) : float_run (option (finite * finite)) :=
  let '(lo, first) := float_full_bound true I in
  let '(hi, second) := float_full_bound false I in
  let '(ordered, compared) := float_nn_compare lo hi in
  let not_upper := negb (nn_is_pinf lo) in
  let not_lower := negb (nn_is_ninf hi) in
  let accept := ordered && not_upper && not_lower in
  let prefix := first ++ second ++ compared ++
    [FloatCase 21; FloatCase 22; FloatBoolean 23 (nn_is_pinf lo) false;
     FloatBoolean 24 ordered not_upper; FloatCase 25; FloatCase 26;
     FloatBoolean 23 (nn_is_ninf hi) false;
     FloatBoolean 24 (ordered && not_upper) not_lower; FloatCase 27] in
  if accept then
    let '(left_bound, left_trace) := float_clamp lo in
    let '(right_bound, right_trace) := float_clamp hi in
    (Some (left_bound, right_bound), prefix ++ left_trace ++ right_trace ++
      [FloatConstruct 28; FloatConstruct 29])
  else (None, prefix ++ [FloatConstruct 29]).

Definition float_class (I : interval) (class : fl_class) : float_run bool :=
  float_mark 30
    (match class with
    | FlNaN => (may_nan I, [FloatProjection 31])
    | FlZero sign =>
      (if sign then may_neg_zero I else may_pos_zero I, [FloatCase 32; FloatProjection 33])
    | FlInfinity sign =>
      let '(active, first) := float_active I in
      let '(included, second) := if sign then float_nn_compare (flo I) fl_ninf
        else float_nn_compare fl_pinf (fhi I) in
      (active && included, first ++ [FloatCase 34; FloatProjection 35;
        FloatConstruct 36; FloatConstruct 37] ++ second ++ [FloatBoolean 38 active included])
    | FlFinite sign =>
      let '(bounds, body) := float_bounds I in
      match bounds with
      | None => (false, body ++ [FloatCase 39])
      | Some (lo, hi) =>
        let '(opposite, compared) := if sign then float_nn_compare fl_zero (fl_finite_nn lo)
          else float_nn_compare (fl_finite_nn hi) fl_zero in
        (negb opposite, body ++ [FloatCase 39; FloatCase 40; FloatConstruct 11;
          FloatConstruct 12; FloatProjection 41; FloatConstruct 42] ++ compared ++
          [FloatBoolean 23 opposite false])
      end
    end).

(** Both lower and upper joins repeat their actual active tests and comparisons. *)
Definition float_join_source (I J : interval) : float_run interval :=
  let bound lower :=
    let '(active_i, first) := float_active I in
    if active_i then
      let '(active_j, second) := float_active J in
      if active_j then
        let '(out, compared) := float_minmax lower
          (if lower then flo I else fhi I) (if lower then flo J else fhi J) in
        (out, first ++ [FloatCase 43] ++ second ++ [FloatCase 44;
          FloatProjection 45; FloatProjection 46] ++ compared)
      else (if lower then flo I else fhi I,
        first ++ [FloatCase 43] ++ second ++ [FloatCase 44; FloatProjection 45])
    else (if lower then flo J else fhi J, first ++ [FloatCase 43; FloatProjection 46]) in
  let '(lo, first) := bound true in
  let '(hi, second) := bound false in
  (FlInterval lo hi (may_nan I || may_nan J) (may_neg_zero I || may_neg_zero J)
    (may_pos_zero I || may_pos_zero J) (may_subnormal I || may_subnormal J),
    first ++ second ++ [FloatProjection 47; FloatProjection 47; FloatBoolean 48 (may_nan I)
      (may_nan J);
      FloatProjection 49; FloatProjection 49; FloatBoolean 48 (may_neg_zero I) (may_neg_zero J);
      FloatProjection 50; FloatProjection 50; FloatBoolean 48 (may_pos_zero I) (may_pos_zero J);
      FloatProjection 51; FloatProjection 51; FloatBoolean 48 (may_subnormal I) (may_subnormal J);
      FloatConstruct 52]).

Definition float_bottom_source : float_run interval :=
  (fl_bottom, [FloatConstruct 36; FloatConstruct 37; FloatConstruct 36;
    FloatConstruct 37; FloatConstruct 52]).

Definition float_pair_source (I J : interval) (a b : fl_class) : float_run interval :=
  let '(left_has, first) := float_class I a in
  let '(right_has, second) := float_class J b in
  let prefix := first ++ second ++ [FloatBoolean 53 left_has right_has; FloatCase 54] in
  if left_has && right_has then
    let result := fl_class_result FDiv a b in
    match result with
    | None => let '(out, bottom_trace) := float_bottom_source in
      (out, prefix ++ [FloatCase 55; FloatCase 56] ++ bottom_trace)
    | Some class =>
      (fl_class_interval class, prefix ++ [FloatCase 55; FloatCase 56; FloatCase 57;
        FloatConstruct 36; FloatConstruct 37; FloatBoolean 23 false false; FloatConstruct 52])
    end
  else let '(out, body) := float_bottom_source in (out, prefix ++ body).

(** Right-folding seven already-computed values preserves fl_join7's exact association. *)
Fixpoint float_join_list (values : list interval) : float_run interval :=
  match values with
  | [] => float_bottom_source
  | [value] => (value, [])
  | value :: rest =>
    let '(tail, first) := float_join_list rest in
    let '(out, second) := float_join_source value tail in (out, first ++ second)
  end.

Definition float_classes : list fl_class :=
  [FlNaN; FlInfinity true; FlInfinity false; FlZero true; FlZero false;
    FlFinite true; FlFinite false].

Definition float_special_row_source I J a : float_run interval :=
  let values := map (float_pair_source I J a) float_classes in
  let '(out, joined) := float_join_list (map fst values) in
  (out, concat (map snd values) ++ joined).

Definition float_special_source I J : float_run interval :=
  let rows := map (float_special_row_source I J) float_classes in
  let '(out, joined) := float_join_list (map fst rows) in
  (out, concat (map snd rows) ++ joined).

Definition float_directed_source (rounding : mode) (fallback : nn) (x y : fl) : float_run nn :=
  let raw := fl_single_bin FDiv rounding x y in
  let from_single := fl_from_single raw in
  (match from_single with Some value => value | None => fallback end,
    [FloatCase 58; FloatCase 59; FloatCase 59;
      FloatDivide rounding x y raw; FloatCase 60] ++
    (match from_single with Some _ => [FloatConstruct 61; FloatConstruct 62;
      FloatConstruct 63] | None => [FloatConstruct 63] end) ++ [FloatCase 64]).

Definition float_corners_source (lower : bool) (a b c d : fl) : float_run nn :=
  let rounding := if lower then mode_DN else mode_UP in
  let fallback := if lower then fl_ninf else fl_pinf in
  let '(first, e1) := float_directed_source rounding fallback a c in
  let '(second, e2) := float_directed_source rounding fallback a d in
  let '(third, e3) := float_directed_source rounding fallback b c in
  let '(fourth, e4) := float_directed_source rounding fallback b d in
  let '(lhs, e5) := float_minmax lower first second in
  let '(rhs, e6) := float_minmax lower third fourth in
  let '(out, e7) := float_minmax lower lhs rhs in
  (out, e1 ++ e2 ++ e3 ++ e4 ++ e5 ++ e6 ++ e7).

(** Every zero test and all three strict subnormal-test operands execute independently. *)
Definition float_bounds_interval_source (lo hi : nn) : float_run interval :=
  let zero_range :=
    let '(first, e1) := float_nn_compare lo fl_zero in
    let '(second, e2) := float_nn_compare fl_zero hi in
    (first && second, e1 ++ e2 ++ [FloatBoolean 65 first second]) in
  let '(negative_zero, z1) := zero_range in
  let '(positive_zero, z2) := zero_range in
  let '(large_lo, s1) := float_nn_compare fl_normal_bound lo in
  let '(large_hi, s2) := float_nn_compare hi (nn_neg fl_normal_bound) in
  let '(nonnegative, s3) := float_nn_compare fl_zero lo in
  let '(nonpositive, s4) := float_nn_compare hi fl_zero in
  (fl_bounds_interval lo hi, z1 ++ z2 ++ [FloatFormatBound true false] ++ s1 ++
    [FloatBoolean 23 large_lo false; FloatFormatBound true false; FloatCase 66;
     FloatBoolean 23 false false; FloatConstruct 67; FloatConstruct 68] ++ s2 ++
    [FloatBoolean 23 large_hi false; FloatBoolean 65 (negb large_lo) (negb large_hi)] ++
    s3 ++ s4 ++ [FloatBoolean 65 nonnegative nonpositive;
      FloatBoolean 23 (nonnegative && nonpositive) false;
      FloatBoolean 65 (negb large_lo && negb large_hi) (negb (nonnegative && nonpositive));
      FloatConstruct 52]).

Definition float_piece_source (a b c d : finite) : float_run interval :=
  let '(ordered, compared) := float_nn_compare (fl_finite_nn c) (fl_finite_nn d) in
  let prefix := [FloatProjection 41; FloatConstruct 42; FloatProjection 41;
    FloatConstruct 42] ++ compared ++ [FloatCase 69] in
  if ordered then
    let '(lo, lower) := float_corners_source true (proj1_sig a) (proj1_sig b)
      (proj1_sig c) (proj1_sig d) in
    let '(hi, upper) := float_corners_source false (proj1_sig a) (proj1_sig b)
      (proj1_sig c) (proj1_sig d) in
    let '(out, built) := float_bounds_interval_source lo hi in
    (out, prefix ++ [FloatProjection 41; FloatProjection 41; FloatProjection 41;
      FloatProjection 41] ++ lower ++ [FloatProjection 41; FloatProjection 41;
      FloatProjection 41; FloatProjection 41] ++ upper ++ built)
  else let '(out, body) := float_bottom_source in (out, prefix ++ body).

Definition float_zero_masks_source (I J raw : interval) : float_run interval :=
  let '(nneg_finite, a) := float_class I (FlFinite true) in
  let '(npos_finite, b) := float_class I (FlFinite false) in
  let '(dneg, c) := float_class J (FlFinite true) in
  let '(dpos, d) := float_class J (FlFinite false) in
  let nneg := may_neg_zero I || nneg_finite in
  let npos := may_pos_zero I || npos_finite in
  let negative := (nneg && dpos) || (npos && dneg) in
  let positive := (nneg && dneg) || (npos && dpos) in
  (audit_float_set_zero_masks I J raw,
    [FloatProjection 70] ++ a ++ [FloatBoolean 71 (may_neg_zero I) nneg_finite;
      FloatProjection 72] ++ b ++ [FloatBoolean 71 (may_pos_zero I) npos_finite] ++ c ++ d ++
    [FloatBoolean 73 nneg dpos; FloatBoolean 73 npos dneg;
     FloatBoolean 71 (nneg && dpos) (npos && dneg); FloatBoolean 73 nneg dneg;
     FloatBoolean 73 npos dpos; FloatBoolean 71 (nneg && dneg) (npos && dpos);
     FloatConstruct 74; FloatCase 75; FloatProjection 3; FloatProjection 4; FloatProjection 31;
     FloatProjection 5; FloatBoolean 73 (may_neg_zero raw) negative;
     FloatProjection 6; FloatBoolean 73 (may_pos_zero raw) positive; FloatProjection 51;
     FloatConstruct 52]).

(** The whole split builds concrete endpoints and composes every finite and exceptional phase. *)
Definition float_div_split_source (I J : interval) : float_run interval :=
  let '(first_bounds, first) := float_bounds I in
  let '(finite_part, finite_trace) := match first_bounds with
    | Some (a, b) =>
      let '(second_bounds, second) := float_bounds J in
      let '(part, trace) := match second_bounds with
      | Some (c, d) =>
      let negative_max := audit_float_negative_endpoint in
      let positive_min := audit_float_positive_endpoint in
      let '(d_order, d_compare) := float_nn_compare (fl_finite_nn d) (fl_finite_nn negative_max) in
      let negative_end := if d_order then d else negative_max in
      let '(negative, negative_trace) := float_piece_source a b c negative_end in
      let '(c_order, c_compare) := float_nn_compare (fl_finite_nn c) (fl_finite_nn positive_min) in
      let positive_end := if c_order then positive_min else c in
      let '(positive, positive_trace) := float_piece_source a b positive_end d in
      let '(joined, join_trace) := float_join_source negative positive in
      let '(out, mask_trace) := float_zero_masks_source I J joined in
      (out, [FloatProjection 41; FloatConstruct 42; FloatProjection 41;
        FloatConstruct 42] ++ d_compare ++ [FloatCase 76] ++ negative_trace ++
        [FloatProjection 41; FloatConstruct 42; FloatProjection 41;
  FloatConstruct 42] ++ c_compare ++ [FloatCase 77] ++ positive_trace ++ join_trace ++
    mask_trace)
      | None => float_bottom_source
      end in (part, second ++ trace)
    | None => float_bottom_source
    end in
  let '(special, special_trace) := float_special_source I J in
  let '(out, joined) := float_join_source finite_part special in
  (out, [FloatEndpoint false; FloatEndpoint true] ++ first ++
    FloatCase 78 :: finite_trace ++ special_trace ++ joined).

(** Primitive size includes tags, sign, mantissa, exponent and NaN payload representation. *)
Definition float_value_bits (value : fl) : nat :=
  match value with
  | @B754_zero _ _ _ | @B754_infinity _ _ _ => 1%nat
  | @B754_nan _ _ _ payload _ => S (Pos.size_nat payload)
  | @B754_finite _ _ _ mantissa exponent _ =>
    (2 + Pos.size_nat mantissa + audit_z_bits exponent)%nat
  end.

(** Numeric exponent distance is retained separately from its encoded bit width. *)
Definition float_alignment_amount (a b : fl) : nat :=
  match a, b with
  | @B754_finite _ _ _ _ ea _, @B754_finite _ _ _ _ eb _ => Z.to_nat (Z.abs (ea - eb))
  | _, _ => 0%nat
  end.

(** The pinned finite division leaf composes its actual core and both numeric rounding alignments.
  *)
Definition float_pinned_division_body (rounding : mode) (a b : fl)
    : list float_body_event :=
  match a, b with
  | @B754_finite _ _ sa ma ea _, @B754_finite _ _ sb mb eb _ =>
    let '((mantissa, exponent, loc), core) :=
      float_body_core prec emax (Z.pos ma) ea (Z.pos mb) eb in
    let '(_, rounded) := float_body_round prec emax rounding (xorb sa sb) mantissa exponent loc in
    [FloatBodyCase 30; FloatBodyCase 31; FloatBodyCase 32] ++ core ++ rounded ++
      [FloatBodyCase 33; FloatBodyBuild 34]
  | _, _ => [FloatBodyCase 30; FloatBodyCase 31; FloatBodyCase 32; FloatBodyBuild 34]
  end.

(** This model retains every actual one-bit rounding step rather than charging its encoded count. *)
Definition float_pinned_division_work rounding a b : nat :=
  S (float_body_work (float_pinned_division_body rounding a b)).

(** This fixed Float-owned primitive model prices Flocq comparison and directed division bodies. *)
Definition float_primitive_body_work (event : float_source_event) : nat :=
  match event with
  | FloatCompare a b _ =>
    let size := (1 + float_value_bits a + float_value_bits b)%nat in
    (1 + size * size + float_alignment_amount a b)%nat
  | FloatDivide rounding a b _ => float_pinned_division_work rounding a b
  | FloatFormatBound _ _ =>
    (10 + audit_z_bits prec + audit_z_bits emax + Z.to_nat (Z.abs prec))%nat
  | FloatInteger a b => audit_binary_weight a b
  | FloatEndpoint _ =>
    (5 + audit_binary_weight 3 emax + audit_binary_weight (3 - emax) prec)%nat
  | _ => 1%nat
  end.

Definition float_source_work (events : list float_source_event) : nat :=
  fold_right (fun event total => (float_primitive_body_work event + total)%nat) 0%nat events.

Definition float_input_size (I J : interval) : nat :=
  (1 + Z.to_nat (Z.abs prec) + Z.to_nat (Z.abs emax) +
    float_value_bits (proj1_sig (flo I)) + float_value_bits (proj1_sig (fhi I)) +
    float_value_bits (proj1_sig (flo J)) + float_value_bits (proj1_sig (fhi J)))%nat.

(** Every primitive body receives a positive fixed source-model charge. *)
Definition float_primitive_body_positive_type : Prop := forall event,
  (0 < float_primitive_body_work event)%nat.

(** The actual finite-core and round outputs used by every division retain the pinned helper
  result. *)
Definition float_pinned_division_body_correspondence_type : Prop :=
  float_body_core_erases_type /\ float_body_round_erases_type /\ float_body_shift_count_type.

(** The whole source result retains every flag and exact signed-zero/NaN observation. *)
Definition float_div_split_source_erases_type : Prop := forall I J,
  fst (float_div_split_source I J) =
    float_div_split I J.

(** This whole abstract bit-work envelope covers both pieces, exceptional table and output. *)
Definition float_div_split_source_bound_type : Prop := forall I J,
  let size := float_input_size I J in
  (float_source_work (snd (float_div_split_source I J)) <=
    10000000 * (size + 1) * (size + 1) * (size + 1) * (size + 1))%nat.

(** The two sign pieces perform at most sixteen directed divisions in this exact execution. *)
Definition float_div_split_source_divides_type : Prop := forall I J,
  (length (filter (fun event =>
    match event with FloatDivide _ _ _ _ => true | _ => false end)
      (snd (float_div_split_source I J))) <= 16)%nat.
Definition float_div_split_source_total_type : Prop := forall I J,
  exists result trace, float_div_split_source I J = (result,trace).
Definition float_div_split_source_unique_type : Prop := forall I J r1 t1 r2 t2,
  float_div_split_source I J=(r1,t1) -> float_div_split_source I J=(r2,t2) ->
  r1=r2 /\ t1=t2.
End FloatSource.
```

### `FloatAuditDivEndpoint.audit_float_min_subnormal_correct`

Card: AUD-FL

Source destination: `theories/Float/FloatAuditDivEndpoint.v`.

```rocq
Theorem audit_float_min_subnormal_correct :
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
Binary.is_finite prec emax (@audit_float_min_subnormal prec emax Hprec Hmax) = true /\
Binary.B2R prec emax (@audit_float_min_subnormal prec emax Hprec Hmax) =
Raux.bpow Zaux.radix2 (3 - emax - prec) /\
(forall x : Binary.binary_float prec emax,
 Binary.is_finite prec emax x = true ->
 Rdefinitions.RbaseSymbolsImpl.Rlt (Rdefinitions.IZR 0) (Binary.B2R prec emax x) ->
 Rdefinitions.Rle (Binary.B2R prec emax (@audit_float_min_subnormal prec emax Hprec Hmax))
   (Binary.B2R prec emax x)).
```

### `FloatAuditDivPlain.audit_float_split_candidate_sound`

Card: AUD-FL

Source destination: `theories/Float/FloatAuditDivPlain.v`.

```rocq
Theorem audit_float_split_candidate_sound :
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax)
  (positive_min negative_max : @FloatOps.fl_finite_bound prec emax),
@audit_float_endpoint_laws prec emax positive_min negative_max ->
forall (nm : @FloatOps.nan_model prec emax) (I J : @FloatInterval.fl_interval prec emax)
  (x y : Binary.binary_float prec emax),
@FloatInterval.fl_gamma prec emax I x ->
@FloatInterval.fl_gamma prec emax J y ->
@FloatInterval.fl_gamma prec emax
  (@audit_float_split_candidate prec emax Hprec Hmax positive_min negative_max I J)
  (@FloatOps.fl_eval_bin prec emax Hprec Hmax nm FloatOps.FDiv x y).
```

### `FloatAuditDiv.float_bin_select_legacy`

Card: AUD-FL

Source destination: `theories/Float/FloatAuditDiv.v`.

```rocq
Theorem float_bin_select_legacy :
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
forall (o : FloatOps.farith) (I J : @FloatInterval.fl_interval prec emax),
@float_bin_select prec emax Hprec Hmax false o I J =
@FloatOps.fl_bin prec emax Hprec Hmax o I J.
```

### `FloatAuditDiv.float_bin_select_sound`

Card: AUD-FL

Source destination: `theories/Float/FloatAuditDiv.v`.

```rocq
Theorem float_bin_select_sound :
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
forall (use_split : bool) (nm : @FloatOps.nan_model prec emax) (o : FloatOps.farith)
  (I J : @FloatInterval.fl_interval prec emax) (x y : Binary.binary_float prec emax),
@FloatInterval.fl_gamma prec emax I x ->
@FloatInterval.fl_gamma prec emax J y ->
@FloatInterval.fl_gamma prec emax (@float_bin_select prec emax Hprec Hmax use_split o I J)
  (@FloatOps.fl_eval_bin prec emax Hprec Hmax nm o x y).
```

### `FloatAuditDiv.float_bin_select_split`

Card: AUD-FL

Source destination: `theories/Float/FloatAuditDiv.v`.

```rocq
Theorem float_bin_select_split :
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
forall I J : @FloatInterval.fl_interval prec emax,
@float_bin_select prec emax Hprec Hmax true FloatOps.FDiv I J =
@float_div_split prec emax Hprec Hmax I J.
```

### `FloatAuditDivBody.float_body_core_erases`

Card: AUD-FL-BODY

Source destination: `theories/Float/FloatAuditDivBody.v`.

```rocq
Theorem float_body_core_erases :
forall prec emax m1 e1 m2 e2 : Z,
@fst (Z * Z * SpecFloat.location) (list float_body_event)
  (float_body_core prec emax m1 e1 m2 e2) =
SpecFloat.SFdiv_core_binary prec emax m1 e1 m2 e2.
```

### `FloatAuditDivBody.float_body_round_erases`

Card: AUD-FL-BODY

Source destination: `theories/Float/FloatAuditDivBody.v`.

```rocq
Theorem float_body_round_erases :
forall (prec emax : Z) (rounding : BinarySingleNaN.mode) (negative : bool)
  (m e : Z) (loc : SpecFloat.location),
@fst SpecFloat.spec_float (list float_body_event)
  (float_body_round prec emax rounding negative m e loc) =
BinarySingleNaN.binary_round_aux prec emax rounding negative m e loc.
```

### `FloatAuditDivBody.float_body_shift_bound`

Card: AUD-FL-BODY

Source destination: `theories/Float/FloatAuditDivBody.v`.

```rocq
Theorem float_body_shift_bound :
forall (fuel : positive) (input : SpecFloat.shr_record),
float_body_work
  (@snd SpecFloat.shr_record (list float_body_event) (float_body_shift_iter fuel input)) <=
10 * Pos.to_nat fuel.
```

### `FloatAuditDivBody.float_body_shift_count`

Card: AUD-FL-BODY

Source destination: `theories/Float/FloatAuditDivBody.v`.

```rocq
Theorem float_body_shift_count :
forall (fuel : positive) (input : SpecFloat.shr_record),
@length float_body_event
  (@filter float_body_event
     (fun event : float_body_event =>
      match event with
      | FloatBodyShiftOne _ _ => true
      | _ => false
      end)
     (@snd SpecFloat.shr_record (list float_body_event) (float_body_shift_iter fuel input))) =
Pos.to_nat fuel.
```

### `FloatAuditDivPrecision.float_div_split_precision`

Card: AUD-FL

Source destination: `theories/Float/FloatAuditDivPrecision.v`.

```rocq
Theorem float_div_split_precision :
forall (Hprec32 : FLX.Prec_gt_0 24) (Hmax32 : BinarySingleNaN.Prec_lt_emax 24 128),
@FloatInterval.fl_gamma 24 128
  (@FloatOps.fl_bin 24 128 Hprec32 Hmax32 FloatOps.FDiv audit_point_one32 audit_zero_to_two32)
  (@proj1_sig (Binary.binary_float 24 128)
     (fun x : Binary.binary_float 24 128 => Binary.is_nan 24 128 x = false) audit_minus_one32) /\
~
@FloatInterval.fl_gamma 24 128
  (@float_div_split 24 128 Hprec32 Hmax32 audit_point_one32 audit_zero_to_two32)
  (@proj1_sig (Binary.binary_float 24 128)
     (fun x : Binary.binary_float 24 128 => Binary.is_nan 24 128 x = false) audit_minus_one32) /\
@FloatInterval.fl_gamma 24 128
  (@float_div_split 24 128 Hprec32 Hmax32 audit_point_one32 audit_zero_to_two32)
  (@proj1_sig (Binary.binary_float 24 128)
     (fun x : Binary.binary_float 24 128 => Binary.is_nan 24 128 x = false)
     (audit_inf32 false)) /\
@FloatInterval.may_neg_zero 24 128
  (@FloatOps.fl_bin 24 128 Hprec32 Hmax32 FloatOps.FDiv audit_positive_zero_only32
     audit_point_one32) =
true /\
@FloatInterval.may_neg_zero 24 128
  (@float_div_split 24 128 Hprec32 Hmax32 audit_positive_zero_only32 audit_point_one32) =
false /\
@FloatInterval.may_pos_zero 24 128
  (@float_div_split 24 128 Hprec32 Hmax32 audit_positive_zero_only32 audit_point_one32) =
true.
```

### `FloatAuditDiv.float_div_split_sound`

Card: AUD-FL

Source destination: `theories/Float/FloatAuditDiv.v`.

```rocq
Theorem float_div_split_sound :
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
forall (nm : @FloatOps.nan_model prec emax) (I J : @FloatInterval.fl_interval prec emax)
  (x y : Binary.binary_float prec emax),
@FloatInterval.fl_gamma prec emax I x ->
@FloatInterval.fl_gamma prec emax J y ->
@FloatInterval.fl_gamma prec emax (@float_div_split prec emax Hprec Hmax I J)
  (@FloatOps.fl_eval_bin prec emax Hprec Hmax nm FloatOps.FDiv x y).
```

### `FloatAuditDivSource.float_div_split_source_bound`

Card: AUD-FL

Source destination: `theories/Float/FloatAuditDivSource.v`.

```rocq
Theorem float_div_split_source_bound :
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
forall I J : @FloatInterval.fl_interval prec emax,
let size := @float_input_size prec emax I J in
@float_source_work prec emax
  (@snd (@FloatInterval.fl_interval prec emax) (list (@float_source_event prec emax))
     (@float_div_split_source prec emax Hprec Hmax I J)) <=
Init.Nat.of_num_uint
  (Number.UIntDecimal
     (Decimal.D1
        (Decimal.D0
           (Decimal.D0
              (Decimal.D0 (Decimal.D0 (Decimal.D0 (Decimal.D0 (Decimal.D0 Decimal.Nil))))))))) *
(size + 1) * (size + 1) * (size + 1) * (size + 1).
```

### `FloatAuditDivSource.float_div_split_source_divides`

Card: AUD-FL

Source destination: `theories/Float/FloatAuditDivSource.v`.

```rocq
Theorem float_div_split_source_divides :
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
forall I J : @FloatInterval.fl_interval prec emax,
@length (@float_source_event prec emax)
  (@filter (@float_source_event prec emax)
     (fun event : @float_source_event prec emax =>
      match event with
      | @FloatDivide _ _ _ _ _ _ => true
      | _ => false
      end)
     (@snd (@FloatInterval.fl_interval prec emax) (list (@float_source_event prec emax))
        (@float_div_split_source prec emax Hprec Hmax I J))) <=
16.
```

### `FloatAuditDivSource.float_div_split_source_erases`

Card: AUD-FL

Source destination: `theories/Float/FloatAuditDivSource.v`.

```rocq
Theorem float_div_split_source_erases :
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
forall I J : @FloatInterval.fl_interval prec emax,
@fst (@FloatInterval.fl_interval prec emax) (list (@float_source_event prec emax))
  (@float_div_split_source prec emax Hprec Hmax I J) =
@float_div_split prec emax Hprec Hmax I J.
```

### `FloatAuditDivSource.float_div_split_source_total`

Card: AUD-FL

Source destination: `theories/Float/FloatAuditDivSource.v`.

```rocq
Theorem float_div_split_source_total :
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
forall I J : @FloatInterval.fl_interval prec emax,
exists
  (result : @FloatInterval.fl_interval prec emax) (trace : list (@float_source_event prec emax)),
  @float_div_split_source prec emax Hprec Hmax I J = (result, trace).
```

### `FloatAuditDivSource.float_div_split_source_unique`

Card: AUD-FL

Source destination: `theories/Float/FloatAuditDivSource.v`.

```rocq
Theorem float_div_split_source_unique :
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
forall (I J r1 : @FloatInterval.fl_interval prec emax)
  (t1 : list (@float_source_event prec emax)) (r2 : @FloatInterval.fl_interval prec emax)
  (t2 : list (@float_source_event prec emax)),
@float_div_split_source prec emax Hprec Hmax I J = (r1, t1) ->
@float_div_split_source prec emax Hprec Hmax I J = (r2, t2) -> r1 = r2 /\ t1 = t2.
```

### `FloatAuditDivSource.float_pinned_division_body_correspondence`

Card: AUD-FL

Source destination: `theories/Float/FloatAuditDivSource.v`.

```rocq
Theorem float_pinned_division_body_correspondence :
float_body_core_erases_type /\ float_body_round_erases_type /\ float_body_shift_count_type.
```

### `FloatAuditDivSource.float_primitive_body_positive`

Card: AUD-FL

Source destination: `theories/Float/FloatAuditDivSource.v`.

```rocq
Theorem float_primitive_body_positive :
forall prec emax : Z,
forall event : @float_source_event prec emax, 0 < @float_primitive_body_work prec emax event.
```

### `FloatAuditDiv.float_zero_sign_sound`

Card: AUD-FL

Source destination: `theories/Float/FloatAuditDiv.v`.

```rocq
Theorem float_zero_sign_sound :
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
forall (nm : @FloatOps.nan_model prec emax) (I J : @FloatInterval.fl_interval prec emax)
  (x y : Binary.binary_float prec emax) (s : bool),
@FloatInterval.fl_gamma prec emax I x ->
@FloatInterval.fl_gamma prec emax J y ->
Binary.B2FF prec emax (@FloatOps.fl_eval_bin prec emax Hprec Hmax nm FloatOps.FDiv x y) =
Binary.F754_zero s ->
(if s
 then @FloatInterval.may_neg_zero prec emax (@float_div_split prec emax Hprec Hmax I J)
 else @FloatInterval.may_pos_zero prec emax (@float_div_split prec emax Hprec Hmax I J)) =
true.
```

### `FloatAuditDiv.select_sound`

Card: AUD-FL

Source destination: `theories/Float/FloatAuditDiv.v`.

```rocq
Theorem select_sound :
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
forall (use_split : bool) (nm : @FloatOps.nan_model prec emax) (o : FloatOps.farith)
  (I J : @FloatInterval.fl_interval prec emax) (x y : Binary.binary_float prec emax),
@FloatInterval.fl_gamma prec emax I x ->
@FloatInterval.fl_gamma prec emax J y ->
@FloatInterval.fl_gamma prec emax (@float_bin_select prec emax Hprec Hmax use_split o I J)
  (@FloatOps.fl_eval_bin prec emax Hprec Hmax nm o x y).
```

### `FloatAuditDiv.split_sound`

Card: AUD-FL

Source destination: `theories/Float/FloatAuditDiv.v`.

```rocq
Theorem split_sound :
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
forall (nm : @FloatOps.nan_model prec emax) (I J : @FloatInterval.fl_interval prec emax)
  (x y : Binary.binary_float prec emax),
@FloatInterval.fl_gamma prec emax I x ->
@FloatInterval.fl_gamma prec emax J y ->
@FloatInterval.fl_gamma prec emax (@float_div_split prec emax Hprec Hmax I J)
  (@FloatOps.fl_eval_bin prec emax Hprec Hmax nm FloatOps.FDiv x y).
```

### `FloatAuditDiv.zero_sign_sound`

Card: AUD-FL

Source destination: `theories/Float/FloatAuditDiv.v`.

```rocq
Theorem zero_sign_sound :
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
forall (nm : @FloatOps.nan_model prec emax) (I J : @FloatInterval.fl_interval prec emax)
  (x y : Binary.binary_float prec emax) (s : bool),
@FloatInterval.fl_gamma prec emax I x ->
@FloatInterval.fl_gamma prec emax J y ->
Binary.B2FF prec emax (@FloatOps.fl_eval_bin prec emax Hprec Hmax nm FloatOps.FDiv x y) =
Binary.F754_zero s ->
(if s
 then @FloatInterval.may_neg_zero prec emax (@float_div_split prec emax Hprec Hmax I J)
 else @FloatInterval.may_pos_zero prec emax (@float_div_split prec emax Hprec Hmax I J)) =
true.
```

<!-- AUD-API-NUM-END -->

<!-- AUD-API-BRIDGE-Float-BEGIN -->

## Galois.Float.FloatAuditCostBridge

Card: AUD-COST-BRIDGE

Source destination: `theories/Float/FloatAuditCostBridge.v`.

```rocq
(** * Float full source bridge

    This root fixes universal proof obligations; no universal proof is claimed here.
    For example, every source budget refers to the fixed canonical operation and actual operands.
    Builds on: the core bridge and the Float source models. *)

From Stdlib Require Import List ZArith NArith PArith Bool.
From Galois.Float Require Import FloatAuditDiv FloatAuditDivBody FloatAuditDivEndpoint
  FloatAuditDivPlain FloatAuditDivPrecision FloatAuditDivSource.
From Galois.Analyses Require Import AnalysesAuditCostBridge.

(** The exponent depends only on the original finite-division inputs. *)
Definition audit_float_div_round_input_size (prec emax m1 e1 m2 e2 : Z) : N :=
  (1 + Z.to_N (Z.abs prec) + Z.to_N (Z.abs emax) + Z.to_N (Z.abs m1) +
    Z.to_N (Z.abs e1) + Z.to_N (Z.abs m2) + Z.to_N (Z.abs e2))%N.

(** This deliberately conservative envelope also covers intermediate shift and power sizes. *)
Definition audit_float_div_round_input_budget (prec emax m1 e1 m2 e2 : Z) : N :=
  N.pow 2 (64 + 8 * audit_float_div_round_input_size prec emax m1 e1 m2 e2).

(** One captured core result feeds the rounding call and both retained source traces. *)
Definition audit_float_div_round_captured (prec emax m1 e1 m2 e2 : Z)
    (rounding : BinarySingleNaN.mode) (negative : bool)
    : SpecFloat.spec_float * (list float_body_event * list float_body_event) :=
  let '(core, core_events) := float_body_core prec emax m1 e1 m2 e2 in
  let '(mantissa, exponent, loc) := core in
  let '(rounded, round_events) :=
    float_body_round prec emax rounding negative mantissa exponent loc in
  (rounded, (core_events, round_events)).

(** The fixed finite execution agrees with its reference and meets its original-input envelope. *)
Definition audit_float_div_round_constructive_statement : Prop :=
  forall prec emax m1 e1 m2 e2 rounding negative,
  let '(rounded, (core_events, round_events)) :=
    audit_float_div_round_captured prec emax m1 e1 m2 e2 rounding negative in
  let '(mantissa, exponent, loc) := SpecFloat.SFdiv_core_binary prec emax m1 e1 m2 e2 in
  rounded = BinarySingleNaN.binary_round_aux prec emax rounding negative mantissa exponent loc /\
  (Z.to_N (Z.abs mantissa) <= audit_float_div_round_input_budget prec emax m1 e1 m2 e2)%N /\
  (Z.to_N (Z.abs exponent) <= audit_float_div_round_input_budget prec emax m1 e1 m2 e2)%N /\
  (N.of_nat (float_body_work core_events + float_body_work round_events) <=
    audit_float_div_round_input_budget prec emax m1 e1 m2 e2)%N.

Definition bridge_audit_float_min_subnormal_correct_type : Prop :=
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
Binary.is_finite prec emax (@audit_float_min_subnormal prec emax Hprec Hmax) = true /\
Binary.B2R prec emax (@audit_float_min_subnormal prec emax Hprec Hmax) =
Raux.bpow Zaux.radix2 (3 - emax - prec) /\
(forall x : Binary.binary_float prec emax,
 Binary.is_finite prec emax x = true ->
 Rdefinitions.RbaseSymbolsImpl.Rlt (Rdefinitions.IZR 0) (Binary.B2R prec emax x) ->
 Rdefinitions.Rle (Binary.B2R prec emax (@audit_float_min_subnormal prec emax Hprec Hmax))
   (Binary.B2R prec emax x)).

Definition bridge_audit_float_split_candidate_sound_type : Prop :=
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax)
  (positive_min negative_max : @FloatOps.fl_finite_bound prec emax),
@audit_float_endpoint_laws prec emax positive_min negative_max ->
forall (nm : @FloatOps.nan_model prec emax) (I J : @FloatInterval.fl_interval prec emax)
  (x y : Binary.binary_float prec emax),
@FloatInterval.fl_gamma prec emax I x ->
@FloatInterval.fl_gamma prec emax J y ->
@FloatInterval.fl_gamma prec emax
  (@audit_float_split_candidate prec emax Hprec Hmax positive_min negative_max I J)
  (@FloatOps.fl_eval_bin prec emax Hprec Hmax nm FloatOps.FDiv x y).

Definition bridge_float_bin_select_legacy_type : Prop :=
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
forall (o : FloatOps.farith) (I J : @FloatInterval.fl_interval prec emax),
@float_bin_select prec emax Hprec Hmax false o I J =
@FloatOps.fl_bin prec emax Hprec Hmax o I J.

Definition bridge_float_bin_select_sound_type : Prop :=
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
forall (use_split : bool) (nm : @FloatOps.nan_model prec emax) (o : FloatOps.farith)
  (I J : @FloatInterval.fl_interval prec emax) (x y : Binary.binary_float prec emax),
@FloatInterval.fl_gamma prec emax I x ->
@FloatInterval.fl_gamma prec emax J y ->
@FloatInterval.fl_gamma prec emax (@float_bin_select prec emax Hprec Hmax use_split o I J)
  (@FloatOps.fl_eval_bin prec emax Hprec Hmax nm o x y).

Definition bridge_float_bin_select_split_type : Prop :=
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
forall I J : @FloatInterval.fl_interval prec emax,
@float_bin_select prec emax Hprec Hmax true FloatOps.FDiv I J =
@float_div_split prec emax Hprec Hmax I J.

Definition bridge_float_body_core_erases_type : Prop :=
forall prec emax m1 e1 m2 e2 : Z,
@fst (Z * Z * SpecFloat.location) (list float_body_event)
  (float_body_core prec emax m1 e1 m2 e2) =
SpecFloat.SFdiv_core_binary prec emax m1 e1 m2 e2.

Definition bridge_float_body_round_erases_type : Prop :=
forall (prec emax : Z) (rounding : BinarySingleNaN.mode) (negative : bool)
  (m e : Z) (loc : SpecFloat.location),
@fst SpecFloat.spec_float (list float_body_event)
  (float_body_round prec emax rounding negative m e loc) =
BinarySingleNaN.binary_round_aux prec emax rounding negative m e loc.

Definition bridge_float_body_shift_bound_type : Prop :=
forall (fuel : positive) (input : SpecFloat.shr_record),
float_body_work
  (@snd SpecFloat.shr_record (list float_body_event) (float_body_shift_iter fuel input)) <=
10 * Pos.to_nat fuel.

Definition bridge_float_body_shift_count_type : Prop :=
forall (fuel : positive) (input : SpecFloat.shr_record),
@length float_body_event
  (@filter float_body_event
     (fun event : float_body_event =>
      match event with
      | FloatBodyShiftOne _ _ => true
      | _ => false
      end)
     (@snd SpecFloat.shr_record (list float_body_event) (float_body_shift_iter fuel input))) =
Pos.to_nat fuel.

Definition bridge_float_div_split_precision_type : Prop :=
forall (Hprec32 : FLX.Prec_gt_0 24) (Hmax32 : BinarySingleNaN.Prec_lt_emax 24 128),
@FloatInterval.fl_gamma 24 128
  (@FloatOps.fl_bin 24 128 Hprec32 Hmax32 FloatOps.FDiv audit_point_one32 audit_zero_to_two32)
  (@proj1_sig (Binary.binary_float 24 128)
     (fun x : Binary.binary_float 24 128 => Binary.is_nan 24 128 x = false) audit_minus_one32) /\
~
@FloatInterval.fl_gamma 24 128
  (@float_div_split 24 128 Hprec32 Hmax32 audit_point_one32 audit_zero_to_two32)
  (@proj1_sig (Binary.binary_float 24 128)
     (fun x : Binary.binary_float 24 128 => Binary.is_nan 24 128 x = false) audit_minus_one32) /\
@FloatInterval.fl_gamma 24 128
  (@float_div_split 24 128 Hprec32 Hmax32 audit_point_one32 audit_zero_to_two32)
  (@proj1_sig (Binary.binary_float 24 128)
     (fun x : Binary.binary_float 24 128 => Binary.is_nan 24 128 x = false)
     (audit_inf32 false)) /\
@FloatInterval.may_neg_zero 24 128
  (@FloatOps.fl_bin 24 128 Hprec32 Hmax32 FloatOps.FDiv audit_positive_zero_only32
     audit_point_one32) =
true /\
@FloatInterval.may_neg_zero 24 128
  (@float_div_split 24 128 Hprec32 Hmax32 audit_positive_zero_only32 audit_point_one32) =
false /\
@FloatInterval.may_pos_zero 24 128
  (@float_div_split 24 128 Hprec32 Hmax32 audit_positive_zero_only32 audit_point_one32) =
true.

Definition bridge_float_div_split_sound_type : Prop :=
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
forall (nm : @FloatOps.nan_model prec emax) (I J : @FloatInterval.fl_interval prec emax)
  (x y : Binary.binary_float prec emax),
@FloatInterval.fl_gamma prec emax I x ->
@FloatInterval.fl_gamma prec emax J y ->
@FloatInterval.fl_gamma prec emax (@float_div_split prec emax Hprec Hmax I J)
  (@FloatOps.fl_eval_bin prec emax Hprec Hmax nm FloatOps.FDiv x y).

Definition bridge_float_div_split_source_bound_type : Prop :=
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
forall I J : @FloatInterval.fl_interval prec emax,
let size := @float_input_size prec emax I J in
@float_source_work prec emax
  (@snd (@FloatInterval.fl_interval prec emax) (list (@float_source_event prec emax))
     (@float_div_split_source prec emax Hprec Hmax I J)) <=
Init.Nat.of_num_uint
  (Number.UIntDecimal
     (Decimal.D1
        (Decimal.D0
           (Decimal.D0
              (Decimal.D0 (Decimal.D0 (Decimal.D0 (Decimal.D0 (Decimal.D0 Decimal.Nil))))))))) *
(size + 1) * (size + 1) * (size + 1) * (size + 1).

Definition bridge_float_div_split_source_divides_type : Prop :=
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
forall I J : @FloatInterval.fl_interval prec emax,
@length (@float_source_event prec emax)
  (@filter (@float_source_event prec emax)
     (fun event : @float_source_event prec emax =>
      match event with
      | @FloatDivide _ _ _ _ _ _ => true
      | _ => false
      end)
     (@snd (@FloatInterval.fl_interval prec emax) (list (@float_source_event prec emax))
        (@float_div_split_source prec emax Hprec Hmax I J))) <=
16.

Definition bridge_float_div_split_source_erases_type : Prop :=
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
forall I J : @FloatInterval.fl_interval prec emax,
@fst (@FloatInterval.fl_interval prec emax) (list (@float_source_event prec emax))
  (@float_div_split_source prec emax Hprec Hmax I J) =
@float_div_split prec emax Hprec Hmax I J.

Definition bridge_float_div_split_source_total_type : Prop :=
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
forall I J : @FloatInterval.fl_interval prec emax,
exists
  (result : @FloatInterval.fl_interval prec emax) (trace : list (@float_source_event prec emax)),
  @float_div_split_source prec emax Hprec Hmax I J = (result, trace).

Definition bridge_float_div_split_source_unique_type : Prop :=
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
forall (I J r1 : @FloatInterval.fl_interval prec emax)
  (t1 : list (@float_source_event prec emax)) (r2 : @FloatInterval.fl_interval prec emax)
  (t2 : list (@float_source_event prec emax)),
@float_div_split_source prec emax Hprec Hmax I J = (r1, t1) ->
@float_div_split_source prec emax Hprec Hmax I J = (r2, t2) -> r1 = r2 /\ t1 = t2.

Definition bridge_float_pinned_division_body_correspondence_type : Prop :=
float_body_core_erases_type /\ float_body_round_erases_type /\ float_body_shift_count_type.

Definition bridge_float_primitive_body_positive_type : Prop :=
forall prec emax : Z,
forall event : @float_source_event prec emax, 0 < @float_primitive_body_work prec emax event.

Definition bridge_float_zero_sign_sound_type : Prop :=
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
forall (nm : @FloatOps.nan_model prec emax) (I J : @FloatInterval.fl_interval prec emax)
  (x y : Binary.binary_float prec emax) (s : bool),
@FloatInterval.fl_gamma prec emax I x ->
@FloatInterval.fl_gamma prec emax J y ->
Binary.B2FF prec emax (@FloatOps.fl_eval_bin prec emax Hprec Hmax nm FloatOps.FDiv x y) =
Binary.F754_zero s ->
(if s
 then @FloatInterval.may_neg_zero prec emax (@float_div_split prec emax Hprec Hmax I J)
 else @FloatInterval.may_pos_zero prec emax (@float_div_split prec emax Hprec Hmax I J)) =
true.

Definition bridge_select_sound_type : Prop :=
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
forall (use_split : bool) (nm : @FloatOps.nan_model prec emax) (o : FloatOps.farith)
  (I J : @FloatInterval.fl_interval prec emax) (x y : Binary.binary_float prec emax),
@FloatInterval.fl_gamma prec emax I x ->
@FloatInterval.fl_gamma prec emax J y ->
@FloatInterval.fl_gamma prec emax (@float_bin_select prec emax Hprec Hmax use_split o I J)
  (@FloatOps.fl_eval_bin prec emax Hprec Hmax nm o x y).

Definition bridge_split_sound_type : Prop :=
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
forall (nm : @FloatOps.nan_model prec emax) (I J : @FloatInterval.fl_interval prec emax)
  (x y : Binary.binary_float prec emax),
@FloatInterval.fl_gamma prec emax I x ->
@FloatInterval.fl_gamma prec emax J y ->
@FloatInterval.fl_gamma prec emax (@float_div_split prec emax Hprec Hmax I J)
  (@FloatOps.fl_eval_bin prec emax Hprec Hmax nm FloatOps.FDiv x y).

Definition bridge_zero_sign_sound_type : Prop :=
forall (prec emax : Z) (Hprec : FLX.Prec_gt_0 prec)
  (Hmax : BinarySingleNaN.Prec_lt_emax prec emax),
forall (nm : @FloatOps.nan_model prec emax) (I J : @FloatInterval.fl_interval prec emax)
  (x y : Binary.binary_float prec emax) (s : bool),
@FloatInterval.fl_gamma prec emax I x ->
@FloatInterval.fl_gamma prec emax J y ->
Binary.B2FF prec emax (@FloatOps.fl_eval_bin prec emax Hprec Hmax nm FloatOps.FDiv x y) =
Binary.F754_zero s ->
(if s
 then @FloatInterval.may_neg_zero prec emax (@float_div_split prec emax Hprec Hmax I J)
 else @FloatInterval.may_pos_zero prec emax (@float_div_split prec emax Hprec Hmax I J)) =
true.

(** The exact future source-family theorem proves this fixed nonempty conjunction. *)
Definition numeric_float_source_family_statement : Prop :=
  bridge_audit_float_min_subnormal_correct_type /\
  bridge_audit_float_split_candidate_sound_type /\
  bridge_float_bin_select_legacy_type /\
  bridge_float_bin_select_sound_type /\
  bridge_float_bin_select_split_type /\
  bridge_float_body_core_erases_type /\
  bridge_float_body_round_erases_type /\
  bridge_float_body_shift_bound_type /\
  bridge_float_body_shift_count_type /\
  bridge_float_div_split_precision_type /\
  bridge_float_div_split_sound_type /\
  bridge_float_div_split_source_bound_type /\
  bridge_float_div_split_source_divides_type /\
  bridge_float_div_split_source_erases_type /\
  bridge_float_div_split_source_total_type /\
  bridge_float_div_split_source_unique_type /\
  bridge_float_pinned_division_body_correspondence_type /\
  bridge_float_primitive_body_positive_type /\
  bridge_float_zero_sign_sound_type /\
  bridge_select_sound_type /\
  bridge_split_sound_type /\
  bridge_zero_sign_sound_type.


(** Float composition includes the complete core family and the fixed Float source family. *)
Definition audit_float_full_source_bridge_statement : Prop :=
  audit_core_full_source_bridge_statement /\ numeric_float_source_family_statement /\
  audit_float_div_round_constructive_statement.
```

Future theorems in `FloatAuditCostBridge`:

```rocq
Theorem audit_float_div_round_constructive :
  audit_float_div_round_constructive_statement.
Theorem audit_float_full_source_bridge : audit_float_full_source_bridge_statement.
```

The finite fixture has a closed proof. The future consumer applies the constructive helper,
and its proof must remain closed.

Test destination: `tests/Float/FloatAuditCostBridgeExamples.v`.

```rocq
(** * A finite Float bridge client

    This fixture checks one finite division and the rounding fed by its result.
    For example, both the division and rounding traces are nonempty.
    Builds on: the finite division body and the pinned Float helpers. *)

From Stdlib Require Import List NArith ZArith PArith Floats.SpecFloat.
From Galois.Float Require Import FloatAuditDivBody FloatAuditCostBridge.

(** This concrete consumer is to be established from the constructive composition theorem. *)
Definition audit_float_full_source_bridge_nonempty_statement : Prop :=
  let mode := BinarySingleNaN.mode_NE in
  let '(rounded, (core_events, round_events)) :=
    audit_float_div_round_captured 24 128 8388608 (-23) 12582912 (-22) mode false in
  let '(mantissa, exponent, loc) :=
    SpecFloat.SFdiv_core_binary 24 128 8388608 (-23) 12582912 (-22) in
  rounded = BinarySingleNaN.binary_round_aux 24 128 mode false mantissa exponent loc /\
  core_events <> nil /\ round_events <> nil /\
  (N.of_nat (float_body_work core_events + float_body_work round_events) <=
    audit_float_div_round_input_budget 24 128 8388608 (-23) 12582912 (-22))%N.

(** One captured division and rounding run satisfies its concrete trace-work bound. *)
Example audit_float_div_round_finite_fixture :
  let mode := BinarySingleNaN.mode_NE in
  let '(rounded, (core_events, round_events)) :=
    audit_float_div_round_captured 24 128 8388608 (-23) 12582912 (-22) mode false in
  let '(reference_m, reference_e, reference_loc) :=
    SpecFloat.SFdiv_core_binary 24 128 8388608 (-23) 12582912 (-22) in
  rounded = BinarySingleNaN.binary_round_aux
    24 128 mode false reference_m reference_e reference_loc /\
  core_events <> nil /\ round_events <> nil /\
  (N.of_nat (float_body_work core_events + float_body_work round_events) <= 100000000)%N.
Proof.
  vm_compute. intuition congruence.
Qed.

Example audit_float_full_source_bridge_nonempty :
  audit_float_full_source_bridge_nonempty_statement.
```

<!-- AUD-API-BRIDGE-Float-END -->
