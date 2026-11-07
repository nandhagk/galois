(** * Floating-point foundations

    This module re-exports the standard-library and Flocq foundations of floating-point intervals.
    For example, an interval client can use real arithmetic and binary floating-point comparison.
    Builds on: Stdlib real arithmetic and Flocq Core and IEEE754. *)

From Stdlib Require Export Bool ZArith Reals Lra Lia.
From Flocq Require Export Core IEEE754.BinarySingleNaN IEEE754.Binary.
