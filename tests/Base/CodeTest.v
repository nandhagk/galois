(** * Composite key tests

    These examples check equality of composite encoded keys.
    For example, reversing distinct pair components changes their keys.
    Builds on: Key and Code. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import Key Code.

Module PosPair := PairKeyCode PosKeyCode PosKeyCode.
Module PosSum := SumKeyCode PosKeyCode PosKeyCode.

Example encoding_only_pair_negative :
  Pos.eqb (PosPair.encode (1%positive, 2%positive))
    (PosPair.encode (2%positive, 1%positive)) = false.
Proof. vm_compute. reflexivity. Qed.

Example encoding_only_sum_negative :
  Pos.eqb (PosSum.encode (inl 1%positive)) (PosSum.encode (inr 1%positive)) = false.
Proof. vm_compute. reflexivity. Qed.

(* BaseCodeTest.tree_roundtrip, recursive_tree_codec, tree_rejects_wrong_arity,
   code_nested_roundtrip, code_rejects_truncation, code_rejects_trailing_bits,
   code_empty_boundary, composite_roundtrips, composite_rejects and
   composite_empty_boundaries exercise the deleted universal tree serializer,
   decoder and codec dictionaries. core section 4 replaces these with glue codes.
   encoding_only_pair_positive and encoding_only_empty_side inspect decoded Node
   shapes and retire for the same reason.
   pair_bits expects 13%N and encoding_only_widths expects (13%N, 7%N, 10%N).
   They fix widths of that deleted Node wire format. Glue codes have a different
   wire format, so those serializer-layout observations retire with code_encode.
   pair_ticks, pair_accounts_for_component_ticks, encoding_only_ticks,
   encoding_only_expensive_ticks and encoding_only_unused_ticks retire with Cost.
   encoding_only_nested_injective and encoding_only_tags are symbolic encoding
   clients. KEY and the composite key functors supply injectivity and equality laws.
   encoding_only_pair_cost, encoding_only_sum_cost and encoding_only_nested_cost_laws
   use the deleted Cost contracts. encoding_pair_codec_wire and
   encoding_sum_codec_wire compare the deleted codec and encoding dictionaries. *)
