(** * Abstract interpretation of ordered actions *)
From Stdlib Require Import List.
From Galois.Base Require Import KeySig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import StateSig.
From Galois.Fixpoint Require Import Query SystemSig.
From Galois.Program Require Import CfgSig.
From Galois.Framework Require Import DenseSig InterpSig.
Import List.ListNotations.

Module InterpCode (P : TYPE) (N : KEY_OPS) (E : TYPE) (C : CFG_OPS P N E)
    (X : KEY_OPS) (L : LANG_OPS) (V : VALUE_DOMAIN_OPS L)
    (A : ACTIONS_OPS P E X L) (D : STATE_DOMAIN_OPS X L V) <: SYSTEM_OPS D.
  Definition prog := P.t.
  Definition key := N.t.
  Definition row := dense_row N.t E.t.
  Definition frame := E.t.
  Definition key_code := N.encode.
  Definition rows p : list row := map Seed (C.entries p) ++ map Flow (C.edges p).
  Definition target p (r : row) : key :=
    match r with Seed n => n | Flow e => C.dst p e end.
  Definition start p (r : row) : query key D.t frame :=
    match r with Seed _ => Ret D.top | Flow e => Ask (C.src p e) e end.
  Definition resume p (e : frame) st : query key D.t frame :=
    Ret (fold_left (fun st a =>
      match a with
      | Assign x ex => D.assign x ex st
      | Havoc x => D.havoc x st
      | Assume g es => D.assume g es st
      end) (A.actions p e) st).
  Definition deps p (r : row) : list key :=
    match r with Seed _ => [] | Flow e => [C.src p e] end.
  Definition sides (_ : prog) (_ : row) : list key := [].
End InterpCode.
