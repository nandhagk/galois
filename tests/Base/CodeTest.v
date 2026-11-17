(** * Composite key tests

    These examples check equality of composite encoded keys.
    For example, reversing distinct pair components changes their keys.
    Builds on: Key and Code.

    Groups:
    - PairTests: codes of pairs, which change when the components are reversed.
    - SumTests: codes of sums, which change with the tag of the value. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import Key Code.

(** * Fixtures *)

(** Pairs of positive keys, encoded componentwise. *)
Module PosPair := PairKeyCode PosKeyCode PosKeyCode.

(** Sums of positive keys, tagged left or right. *)
Module PosSum := SumKeyCode PosKeyCode PosKeyCode.

(** * Pair codes *)

Module PairTests.

  (** Reversing the components of a pair gives a different code. *)
  Example reversed_pair_codes_differ :
    Pos.eqb (PosPair.encode (1%positive, 2%positive))
      (PosPair.encode (2%positive, 1%positive)) = false.
  Proof. vm_compute. reflexivity. Qed.

End PairTests.

(** * Sum codes *)

Module SumTests.

  (** The left and right tags of the same value give different codes. *)
  Example left_and_right_tags_differ :
    Pos.eqb (PosSum.encode (inl 1%positive)) (PosSum.encode (inr 1%positive)) = false.
  Proof. vm_compute. reflexivity. Qed.

End SumTests.

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
