(** * Simple lattices

    Boolean and unit carriers have simple lattice operations.
    For example, joining false and true gives true.
    Builds on: LatticeSig and Argent time interfaces. *)

From Stdlib Require Import Bool Arith Lia.
From Argent Require Import Time.
From Galois.Lattice Require Import LatticeSig.

Module BoolLatCode <: BLATTICE_OPS.
  Definition t := bool.
  Definition leb := implb.
  Definition bot := false.
  Definition is_bot := negb.
  Definition join := orb.
  Definition top := true.
  Definition meet := andb.
End BoolLatCode.

Module UnitLatCode <: BLATTICE_OPS.
  Definition t := unit.
  Definition leb (_ _ : t) := true.
  Definition bot := tt.
  Definition is_bot (_ : t) := true.
  Definition join (_ _ : t) := tt.
  Definition top := tt.
  Definition meet (_ _ : t) := tt.
End UnitLatCode.
