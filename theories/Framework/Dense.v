(** * Dense dataflow systems *)
From Stdlib Require Import List.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig.
From Galois.Program Require Import CfgSig.
From Galois.Framework Require Import DenseSig.
Import List.ListNotations.

Module DenseCode (P : TYPE) (N : KEY_OPS) (E : TYPE)
    (C : CFG_OPS P N E) (L : LATTICE_OPS) (T : FLOW_OPS P N E L)
    <: SYSTEM_OPS L.
  Definition prog := P.t.
  Definition key := N.t.
  Definition row := dense_row N.t E.t.
  Definition frame := E.t.
  Definition key_code := N.encode.
  Definition rows p : list row := map Seed (C.entries p) ++ map Flow (C.edges p).
  Definition target p (r : row) : key :=
    match r with
    | Seed n => n
    | Flow e => match T.dir with Forward => C.dst p e | Backward => C.src p e end
    end.
  Definition start p (r : row) : query key L.t frame :=
    match r with
    | Seed n => Ret (T.boundary p n)
    | Flow e => Ask (match T.dir with Forward => C.src p e | Backward => C.dst p e end) e
    end.
  Definition resume p (e : frame) a : query key L.t frame := Ret (T.transfer p e a).
  Definition deps p (r : row) : list key :=
    match r with
    | Seed _ => []
    | Flow e => [match T.dir with Forward => C.src p e | Backward => C.dst p e end]
    end.
  Definition sides (_ : prog) (_ : row) : list key := [].
End DenseCode.
