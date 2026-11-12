(** * Full solution checking

    The checker evaluates each row and checks every value written by the row. *)

From Stdlib Require Import List.
From Galois.Base Require Import MapSig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig CheckSig.

Module CheckCode (L : LATTICE_OPS) (S : SYSTEM_OPS L) <: CHECK_OPS L S.
  Definition look (m : kmap S.key L.t) (x : S.key) : L.t :=
    look_or S.key_code L.bot m x.

  Definition check_rows (p : S.prog) (rs : list S.row) (m : kmap S.key L.t) : bool :=
    forallb (fun r => row_ok L.leb (look m) (S.target p r)
      (eval_query (S.resume p) (look m) (S (length (S.deps p r))) (S.start p r))) rs.

  Definition check (p : S.prog) (m : kmap S.key L.t) : bool :=
    check_rows p (S.rows p) m.
End CheckCode.
